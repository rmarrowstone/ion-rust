use crate::binary::constants::v1_0::{length_codes, IVM};
use crate::binary::header::Header;
use crate::binary::int::DecodedInt;
use crate::binary::non_blocking::binary_buffer::BinaryBuffer;
use crate::binary::uint::DecodedUInt;
use crate::binary::var_uint::VarUInt;
use crate::binary::IonTypeCode;
use crate::result::{
    decoding_error, decoding_error_raw, illegal_operation, illegal_operation_raw,
    incomplete_data_error,
};
use crate::types::integer::UInteger;
use crate::types::SymbolId;
use crate::{
    Decimal, Integer, IonError, IonResult, IonType, RawStreamItem, RawSymbolToken, Timestamp,
};
use bytes::{BigEndian, Buf, ByteOrder};
use num_traits::Zero;
use std::fmt::Display;
use std::io::Read;
use std::ops::Range;

struct ValueHeader {
    stream_offset: usize,
    field_id_bytes: u8,
    annotations_bytes: u8,
    var_length_bytes: u8,
}

/// Information about the value over which the RawBinaryReader is currently positioned.
#[derive(Clone, Debug, PartialEq)]
struct EncodedValue {
    // `EncodedValue` instances are moved during `step_in` and `step_out` operations.
    // If the compiler decides that a value is too large to be moved with inline code,
    // it will relocate the value using memcpy instead. This can be quite slow by comparison.
    //
    // Be cautious when adding new member fields or modifying the data types of existing member
    // fields, as this may cause the in-memory size of `EncodedValue` instances to grow.
    //
    // See the Rust Performance Book section on measuring type sizes[1] for more information.
    // [1] https://nnethercote.github.io/perf-book/type-sizes.html#measuring-type-sizes
    header: Header,
    field_id: Option<RawSymbolToken>,

    // Each encoded value has up to five components, appearing in the following order:
    //
    // [ field_id? | annotations? | header (type descriptor) | header_length? | value ]
    //
    // Components shown with a `?` are optional.
    //
    // EncodedValue stores the offset of the type descriptor byte from the beginning of the
    // data source (`header_offset`). The lengths of the other fields can be used to calculate
    // their positions relative to the type descriptor byte.

    // The number of bytes used to encode the field ID (if present) preceding the Ion value. If
    // `field_id` is undefined, `field_id_length` will be zero.
    field_id_length: u8,
    // The number of bytes used to encode the annotations wrapper (if present) preceding the Ion
    // value. If `annotations` is empty, `annotations_length` will be zero.
    annotations_header_length: u8,
    // The number of bytes used to encode the series of symbol IDs inside the annotations wrapper.
    annotations_sequence_length: u8,
    // Type descriptor byte location.
    header_offset: usize,
    // The number of bytes used to encode the header not including the type descriptor byte.
    header_length: u8,
    // The number of bytes used to encode the value itself, not including the header byte
    // or length fields.
    value_length: usize,
}

impl EncodedValue {
    /// Returns the offset of the current value's type descriptor byte.
    fn header_offset(&self) -> usize {
        self.header_offset as usize
    }

    /// Returns the length of this value's header, including the type descriptor byte and any
    /// additional bytes used to encode the value's length.
    fn header_length(&self) -> usize {
        // The `header_length` field does not include the type descriptor byte, so add 1.
        self.header_length as usize + 1
    }

    /// Returns an offset Range containing this value's type descriptor
    /// byte and any additional bytes used to encode the `length`.
    fn header_range(&self) -> Range<usize> {
        let start = self.header_offset;
        let end = start + self.header_length();
        start..end
    }

    /// Returns the number of bytes used to encode this value's data.
    /// If the value can fit in the type descriptor byte (e.g. `true`, `false`, `null`, `0`),
    /// this function will return 0.
    #[inline(always)]
    fn value_length(&self) -> usize {
        self.value_length
    }

    /// The offset of the first byte following the header (and length, if present).
    /// If `value_length()` returns zero, this offset is actually the first byte of
    /// the next encoded value and should not be read.
    fn value_offset(&self) -> usize {
        self.header_offset + self.header_length as usize + 1_usize
    }

    /// Returns an offset Range containing any bytes following the header.
    fn value_range(&self) -> Range<usize> {
        let start = self.value_offset();
        let end = start + self.value_length;
        start..end
    }

    /// Returns the index of the first byte that is beyond the end of the current value's encoding.
    fn value_end_exclusive(&self) -> usize {
        self.value_offset() + self.value_length
    }

    /// Returns the number of bytes used to encode this value's field ID, if present.
    fn field_id_length(&self) -> Option<usize> {
        self.field_id.as_ref()?;
        Some(self.field_id_length as usize)
    }

    /// Returns the offset of the first byte used to encode this value's field ID, if present.
    fn field_id_offset(&self) -> Option<usize> {
        self.field_id.as_ref()?;
        Some(
            self.header_offset
                - self.annotations_header_length as usize
                - self.field_id_length as usize,
        )
    }

    /// Returns an offset Range that contains the bytes used to encode this value's field ID,
    /// if present.
    fn field_id_range(&self) -> Option<Range<usize>> {
        if let Some(start) = self.field_id_offset() {
            let end = start + self.field_id_length as usize;
            return Some(start..end);
        }
        None
    }

    /// Returns the number of bytes used to encode this value's annotations, if any.
    /// While annotations envelope the value that they decorate, this function does not include
    /// the length of the value itself.
    fn annotations_header_length(&self) -> Option<usize> {
        if self.annotations_header_length == 0 {
            return None;
        }
        Some(self.annotations_header_length as usize)
    }

    fn annotations_sequence_length(&self) -> Option<usize> {
        if self.annotations_header_length == 0 {
            return None;
        }
        Some(self.annotations_sequence_length as usize)
    }

    /// Returns the offset of the beginning of the annotations wrapper, if present.
    fn annotations_offset(&self) -> Option<usize> {
        if self.annotations_header_length == 0 {
            return None;
        }
        Some(self.header_offset - self.annotations_header_length as usize)
    }

    /// Returns an offset Range that includes the bytes used to encode this value's annotations,
    /// if any. While annotations envelope the value that they modify, this function does not
    /// include the bytes of the encoded value itself.
    fn annotations_range(&self) -> Option<Range<usize>> {
        if let Some(start) = self.annotations_offset() {
            let end = start + self.annotations_header_length as usize;
            return Some(start..end);
        }
        None
    }

    /// Returns the total number of bytes used to represent the current value, including the
    /// field ID (if any), its annotations (if any), its header (type descriptor + length bytes),
    /// and its value.
    fn total_length(&self) -> usize {
        self.field_id_length().unwrap_or(0)
            + self.annotations_header_length().unwrap_or(0)
            + self.header_length()
            + self.value_length()
    }
}

impl Default for EncodedValue {
    fn default() -> EncodedValue {
        EncodedValue {
            header: Header {
                ion_type: None,
                ion_type_code: IonTypeCode::NullOrNop,
                length_code: length_codes::NULL,
            },
            field_id: None,
            field_id_length: 0,
            annotations_header_length: 0,
            annotations_sequence_length: 0,
            header_offset: 0,
            header_length: 0,
            value_length: 0,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
enum ReaderState {
    OnIvm,
    OnValue(EncodedValue),
    Skipping(usize), // Need to move `usize` bytes ahead to get to the next thing
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum ContainerType {
    List,
    SEXpression,
    Struct,
}

impl ContainerType {
    pub fn ion_type(&self) -> IonType {
        match self {
            ContainerType::List => IonType::List,
            ContainerType::SEXpression => IonType::SExpression,
            ContainerType::Struct => IonType::Struct,
        }
    }
}

// What kind of container we're in and the ending offset, if known.
#[derive(Debug, PartialEq, Clone, Copy)]
struct Container {
    kind: ContainerType,
    // The offset of the first byte *after* the parent container.
    // If the container starts at index 0 and is 4 bytes long, `exclusive_end` will be `4`.
    exclusive_end: usize,
}

#[derive(Debug)]
pub struct RawBinaryBufferReader<A: AsRef<[u8]>> {
    ion_version: (u8, u8),
    state: ReaderState,
    buffer: BinaryBuffer<A>,
    parents: Vec<Container>,
}

impl<A: AsRef<[u8]>> RawBinaryBufferReader<A> {
    pub fn new(source: A) -> RawBinaryBufferReader<A> {
        RawBinaryBufferReader {
            ion_version: (1, 0),
            state: ReaderState::Skipping(0),
            buffer: BinaryBuffer::new(source),
            parents: Vec::new(), // Does not allocate yet
        }
    }

    fn transaction_reader(&mut self) -> TxReader<A> {
        let RawBinaryBufferReader {
            ion_version,
            state,
            buffer,
            parents,
        } = self;

        let tx_buffer = buffer.slice();
        TxReader {
            ion_version: *ion_version,
            state,
            main_buffer: buffer,
            parent: parents.last(),
            tx_buffer,
            encoded_value: Default::default(),
        }
    }

    fn advance_to_next_item(&mut self) -> IonResult<()> {
        use ReaderState::*;
        match &mut self.state {
            // The 'skipping' state means we ran out of data on a previous call to `next()`. The
            // only way to fix it is to add more input bytes to the buffer. Adding input bytes to the
            // buffer is only supported when A=Vec<u8>.
            Skipping(0) => {
                // Done skipping!
                Ok(())
            }
            Skipping(bytes_to_skip) => {
                let remaining = self.buffer.remaining();
                if remaining >= *bytes_to_skip {
                    self.buffer.consume(*bytes_to_skip);
                    *bytes_to_skip = 0;
                    Ok(())
                } else {
                    self.buffer.consume(remaining);
                    *bytes_to_skip -= remaining;
                    incomplete_data_error("ahead to next item", self.buffer.total_consumed())
                }
            }
            OnIvm => {
                if self.buffer.remaining() < IVM.len() {
                    return incomplete_data_error(
                        "item after Ion version marker",
                        self.buffer.total_consumed(),
                    );
                }
                self.buffer.consume(IVM.len());
                self.state = Skipping(0);
                Ok(())
            }
            OnValue(encoded_value) => {
                let bytes_to_skip = encoded_value.total_length();
                let remaining_bytes = self.buffer.remaining();
                if remaining_bytes < bytes_to_skip {
                    self.buffer.consume(remaining_bytes);
                    self.state = Skipping(bytes_to_skip - remaining_bytes);
                    return incomplete_data_error(
                        "ahead to next item",
                        self.buffer.total_consumed(),
                    );
                }
                self.buffer.consume(bytes_to_skip);
                self.state = Skipping(0);
                Ok(())
            }
        }
    }

    // Reads the next IVM or value header in the stream. Only records offset information. Does not
    // materialize any value data.
    pub fn next(&mut self) -> IonResult<RawStreamItem> {
        // This is the only method that can modify `self.buffer`. It causes the bytes
        // representing the current value to be consumed. If the buffer contains enough data, its
        // new position will be the first byte of the next value (which may be a field_id, annotation,
        // or type_descriptor). If there is not enough data, `self.state` will be set to `Skipping(n)`
        // to keep track of how many more bytes we would need to add to the buffer before we could
        // reach the next value. If `self.state` is `Skipping(n)`, the only way to advance is to add
        // more data to the buffer.
        self.advance_to_next_item()?;

        // Make a 'transaction' reader. This is a slice of our actual input buffer; it's reading the
        // same input bytes, but keeps its own records of how many bytes have been consumed. If
        // reading fails at some point due to incomplete data or another error, the `tx_reader` can
        // be discarded without affecting `self.buffer`.
        let tx_reader = self.transaction_reader();

        // Peek at the first byte of the next value; it could be a field ID, an annotation wrapper,
        // or a value header.
        let type_descriptor = tx_reader.tx_buffer.peek_type_descriptor()?;

        if tx_reader.is_in_struct() {
            // If we're inside a struct, read a (fieldID, value_header) pair.
            tx_reader.read_struct_field_header()
        } else {
            // Otherwise, read a (possibly annotated) value header.
            tx_reader.read_value_header(type_descriptor)
        }
    }

    pub fn annotations(&self) -> impl Iterator<Item = RawSymbolToken> + '_ {
        if let ReaderState::OnValue(encoded_value) = &self.state {
            if let Some(length) = encoded_value.annotations_sequence_length() {
                let header_relative_offset =
                    encoded_value.header_offset - self.buffer.total_consumed();
                let start = header_relative_offset - length;
                let annotations_bytes = &self.buffer.bytes()[start..header_relative_offset];
                return AnnotationsIterator::new(annotations_bytes);
            }
        }
        AnnotationsIterator::new(&self.buffer.bytes()[0..0])
    }

    fn encoded_value(&self) -> Option<&EncodedValue> {
        match &self.state {
            ReaderState::OnValue(encoded_value) => Some(encoded_value),
            _ => None,
        }
    }

    pub fn step_in(&mut self) -> IonResult<()> {
        let value = self.encoded_value().ok_or_else(|| {
            illegal_operation_raw(format!(
                "cannot step in; the reader is not positioned over a container"
            ))
        })?;

        let container_type = match value.header.ion_type.unwrap() {
            IonType::List => ContainerType::List,
            IonType::SExpression => ContainerType::SEXpression,
            IonType::Struct => ContainerType::Struct,
            other => {
                return illegal_operation(format!(
                    "cannot step into a {}; it is not a container",
                    other
                ))
            }
        };

        let container = Container {
            kind: container_type,
            exclusive_end: self.buffer.total_consumed() + value.total_length(),
        };

        // Move the reader to the first byte within the container's value
        let bytes_to_skip = value.total_length() - value.value_length();
        // The buffer will always contain enough bytes to perform this skip; it had to read all of
        // those bytes in order to be parked on this container in the first place.
        self.buffer.consume(bytes_to_skip);
        // The reader is no longer positioned over a value
        self.state = ReaderState::Skipping(0);

        self.parents.push(container);

        Ok(())
    }

    pub fn step_out(&mut self) -> IonResult<()> {
        let parent = match self.parents.pop() {
            Some(parent) => parent,
            None => return illegal_operation("reader cannot step out at the top level (depth=0)"),
        };

        // We need to advance the reader to the first byte beyond the end of the parent container.
        // We'll skip as many bytes as we can from the current buffer, which may or may not be enough.
        let bytes_to_skip = parent.exclusive_end - self.buffer.total_consumed();
        let bytes_skipped = bytes_to_skip.min(self.buffer.remaining());
        // The number of bytes that we still need to skip before the reader can start reading
        // the next value.
        let bytes_left_to_skip = bytes_to_skip - bytes_skipped;
        self.buffer.consume(bytes_skipped);
        // Set the reader state to `Skipping`; if there are still bytes to be skipped, the next
        // call to `next()` will return IonError::Incomplete
        self.state = ReaderState::Skipping(bytes_left_to_skip);

        Ok(())
    }

    pub fn depth(&self) -> usize {
        self.parents.len()
    }

    pub fn parent_type(&self) -> Option<IonType> {
        self.parents.last().map(|c| c.kind.ion_type())
    }

    /// Constructs an [IonError::IllegalOperation] which explains that the reader was asked to
    /// perform an action that is only allowed when it is positioned over the item type described
    /// by the parameter `expected`.
    fn expected<E: Display>(&self, expected: E) -> IonError {
        let encoded_value = self.encoded_value();
        if encoded_value.is_none() {
            return illegal_operation_raw(
                format!(
                    "type mismatch: expected a(n) {} but the reader is not currently positioned on a value",
                    expected
                )
            );
        }
        illegal_operation_raw(format!(
            "type mismatch: expected a(n) {} but positioned over a(n) {}",
            expected,
            encoded_value.unwrap().header.ion_type.unwrap()
        ))
    }

    #[inline]
    fn value_and_bytes<D: Display>(
        &mut self,
        label: D,
        expected_ion_type: IonType,
    ) -> IonResult<(&EncodedValue, &[u8])> {
        // Get a reference to the EncodedValue. This is only possible if the reader is parked
        // on a value.
        let encoded_value = self.encoded_value().ok_or_else(|| {
            illegal_operation_raw(format!(
                "cannot read {}; reader is not positioned on a value",
                label
            ))
        })?;

        // If the value we're parked on is not of the type we're expecting to read, return an error.
        let value_ion_type = encoded_value.header.ion_type.unwrap();
        if value_ion_type != expected_ion_type {
            return illegal_operation(format!(
                "type mismatch: expected a(n) {} but positioned over a(n) {}",
                label, value_ion_type
            ));
        }

        // Make sure that the value's entire representation is available in the buffer. If it's not,
        // return an IonError::Incomplete.
        if self.buffer.remaining() < encoded_value.total_length() {
            return incomplete_data_error(
                "attempted to read a string that was not completely buffered",
                self.buffer.total_consumed(),
            );
        }

        // Get the slice of buffer bytes that represent the value. This slice may be empty.
        let start = encoded_value.total_length() - encoded_value.value_length();
        let end = encoded_value.total_length();
        let bytes = &self.buffer.bytes()[start..end];

        Ok((encoded_value, bytes))
    }

    #[inline]
    fn value_and_buffer<D: Display>(
        &mut self,
        label: D,
        expected_ion_type: IonType,
    ) -> IonResult<(&EncodedValue, BinaryBuffer<&[u8]>)> {
        let (encoded_value, bytes) = self.value_and_bytes(label, expected_ion_type)?;
        Ok((encoded_value, BinaryBuffer::new(bytes)))
    }

    pub fn read_null(&mut self) -> IonResult<IonType> {
        if let Some(value) = self.encoded_value() {
            // If the reader is on a value, the IonType is present.
            let ion_type = value.header.ion_type.unwrap();
            return if value.header.is_null() {
                Ok(ion_type)
            } else {
                illegal_operation(format!(
                    "cannot read null; reader is currently positioned on a non-null {}",
                    ion_type
                ))
            };
        }
        Err(self.expected("null value"))
    }

    pub fn read_bool(&mut self) -> IonResult<bool> {
        let (encoded_value, _) = self.value_and_bytes("a bool", IonType::Boolean)?;

        let representation = encoded_value.header.length_code;
        match representation {
            0 => Ok(false),
            1 => Ok(true),
            _ => decoding_error(format!(
                "found a boolean value with an illegal representation (must be 0 or 1): {}",
                representation
            )),
        }
    }

    pub fn read_integer(&mut self) -> IonResult<Integer> {
        let (encoded_value, mut buffer) = self.value_and_buffer("an int", IonType::Integer)?;
        let uint: DecodedUInt = buffer.read_uint(encoded_value.value_length())?;
        let value = Integer::from(uint);

        use self::IonTypeCode::*;
        let value = match (encoded_value.header.ion_type_code, value) {
            (PositiveInteger, integer) => integer,
            (NegativeInteger, integer) if integer.is_zero() => {
                return decoding_error("found a negative integer (typecode=3) with a value of 0");
            }
            (NegativeInteger, integer) => -integer,
            itc => unreachable!("Unexpected IonTypeCode: {:?}", itc),
        };

        Ok(value)
    }

    pub fn read_f64(&mut self) -> IonResult<f64> {
        let (encoded_value, bytes) = self.value_and_bytes("a float", IonType::Float)?;
        let number_of_bytes = encoded_value.value_length();
        let value = match number_of_bytes {
            0 => 0f64,
            4 => f64::from(BigEndian::read_f32(bytes)),
            8 => BigEndian::read_f64(bytes),
            _ => {
                return decoding_error(&format!(
                    "encountered a float with an illegal length (must be 0, 4, or 8): {}",
                    number_of_bytes
                ))
            }
        };
        Ok(value)
    }

    fn read_decimal(&mut self) -> IonResult<Decimal> {
        let (encoded_value, mut buffer) = self.value_and_buffer("a decimal", IonType::Decimal)?;

        if encoded_value.value_length() == 0 {
            return Ok(Decimal::new(0i32, 0i64));
        }

        let exponent_var_int = buffer.read_var_int()?;
        let coefficient_size_in_bytes =
            encoded_value.value_length() - exponent_var_int.size_in_bytes();

        let exponent = exponent_var_int.value() as i64;
        let coefficient = buffer.read_int(coefficient_size_in_bytes)?;

        if coefficient.is_negative_zero() {
            return Ok(Decimal::negative_zero_with_exponent(exponent));
        }

        Ok(Decimal::new(coefficient, exponent))
    }

    fn read_timestamp(&mut self) -> IonResult<Timestamp> {
        let (encoded_value, mut buffer) =
            self.value_and_buffer("a timestamp", IonType::Timestamp)?;

        let offset = buffer.read_var_int()?;
        let is_known_offset = !offset.is_negative_zero();
        let offset_minutes = offset.value() as i32;
        let year = buffer.read_var_uint()?.value() as u32;

        // Year precision

        let builder = Timestamp::with_year(year);
        if buffer.is_empty() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        // Month precision

        let month = buffer.read_var_uint()?.value() as u32;
        let builder = builder.with_month(month);
        if buffer.is_empty() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        // Day precision

        let day = buffer.read_var_uint()?.value() as u32;
        let builder = builder.with_day(day);
        if buffer.is_empty() {
            let timestamp = builder.build()?;
            return Ok(timestamp);
        }

        // Hour-and-minute precision

        let hour = buffer.read_var_uint()?.value() as u32;
        if buffer.is_empty() {
            return decoding_error("timestamps with an hour must also specify a minute");
        }
        let minute = buffer.read_var_uint()?.value() as u32;
        let builder = builder.with_hour_and_minute(hour, minute);
        if buffer.is_empty() {
            let timestamp = if is_known_offset {
                builder.build_utc_fields_at_offset(offset_minutes)
            } else {
                builder.build_at_unknown_offset()
            }?;
            return Ok(timestamp);
        }

        // Second precision

        let second = buffer.read_var_uint()?.value() as u32;
        let builder = builder.with_second(second);
        if buffer.is_empty() {
            let timestamp = if is_known_offset {
                builder.build_utc_fields_at_offset(offset_minutes)
            } else {
                builder.build_at_unknown_offset()
            }?;
            return Ok(timestamp);
        }

        // Fractional second precision

        let subsecond_exponent = buffer.read_var_int()?.value();
        // The remaining bytes represent the coefficient.
        let coefficient_size_in_bytes = encoded_value.value_length() - buffer.total_consumed();
        let subsecond_coefficient = if coefficient_size_in_bytes == 0 {
            DecodedInt::zero()
        } else {
            buffer.read_int(coefficient_size_in_bytes)?
        };

        let builder = builder
            .with_fractional_seconds(Decimal::new(subsecond_coefficient, subsecond_exponent));
        let timestamp = if is_known_offset {
            builder.build_utc_fields_at_offset(offset_minutes)
        } else {
            builder.build_at_unknown_offset()
        }?;

        Ok(timestamp)
    }

    pub fn read_symbol_id(&mut self) -> IonResult<SymbolId> {
        let (encoded_value, mut buffer) = self.value_and_buffer("a symbol", IonType::Symbol)?;
        match buffer.read_uint(encoded_value.value_length())?.value() {
            UInteger::U64(symbol_id) => {
                let sid = usize::try_from(*symbol_id).map_err(|_| {
                    decoding_error_raw("found a symbol ID that was too large to fit in a usize")
                })?;
                Ok(sid)
            }
            UInteger::BigUInt(_too_big) => {
                decoding_error("found a symbol ID that was too large to fit in a usize")
            }
        }
    }

    pub fn read_str(&mut self) -> IonResult<&str> {
        let (_encoded_value, bytes) = self.value_and_bytes("a string", IonType::String)?;

        let text = std::str::from_utf8(bytes).map_err(|e| {
            decoding_error_raw(format!("encountered invalid utf8 in string: {:?}", e))
        })?;

        Ok(text)
    }

    pub fn read_blob(&mut self) -> IonResult<&[u8]> {
        let (_encoded_value, bytes) = self.value_and_bytes("a blob", IonType::Blob)?;
        Ok(bytes)
    }

    pub fn read_clob(&mut self) -> IonResult<&[u8]> {
        let (_encoded_value, bytes) = self.value_and_bytes("a clob", IonType::Clob)?;
        Ok(bytes)
    }
}

impl RawBinaryBufferReader<Vec<u8>> {
    fn append_bytes(&mut self, bytes: &[u8]) {
        self.buffer.append_bytes(bytes);
    }

    fn read_from<R: Read>(&mut self, source: R, length: usize) -> IonResult<usize> {
        self.buffer.read_from(source, length)
    }
}

struct AnnotationsIterator<'a> {
    data: std::io::Cursor<&'a [u8]>,
}

impl<'a> AnnotationsIterator<'a> {
    pub(crate) fn new(bytes: &[u8]) -> AnnotationsIterator {
        AnnotationsIterator {
            data: std::io::Cursor::new(bytes),
        }
    }
}

impl<'a> Iterator for AnnotationsIterator<'a> {
    type Item = RawSymbolToken;

    fn next(&mut self) -> Option<Self::Item> {
        if self.data.remaining() == 0 {
            return None;
        }
        // This iterator cannot be created unless the reader is currently parked on a value.
        // If the reader is parked on a value, the complete annotations sequence is in the buffer.
        // Therefore, reading symbol IDs from this byte slice cannot fail. This allows us to safely
        // unwrap the result of this `read` call.
        let var_uint = VarUInt::read(&mut self.data).unwrap();
        Some(RawSymbolToken::SymbolId(var_uint.value()))
    }
}

struct TxReader<'a, A: AsRef<[u8]>> {
    ion_version: (u8, u8),
    state: &'a mut ReaderState,
    main_buffer: &'a BinaryBuffer<A>,
    parent: Option<&'a Container>,
    tx_buffer: BinaryBuffer<&'a A>,
    encoded_value: EncodedValue,
}

impl<'a, A: AsRef<[u8]>> TxReader<'a, A> {
    fn read_value_header(self, header: Header) -> IonResult<RawStreamItem> {
        if header.is_annotation_wrapper() {
            self.read_annotated_value_header(header)
        } else {
            self.read_unannotated_value_header(header)
        }
    }

    fn read_struct_field_header(mut self) -> IonResult<RawStreamItem> {
        let mut field_id: VarUInt;
        // NOP padding makes this slightly convoluted. We always read the field ID, but if the value
        // is a NOP then we discard the field ID, read past the NOP, and then start the process again.
        let mut nop_byte_count: usize = 0;
        let mut type_descriptor;
        let stream_item = loop {
            // We need to check this before each attempt at reading a field.
            // It's possible to create a struct with NOP padding but no values.
            if self.is_at_end_of_container() {
                return Ok(RawStreamItem::Nothing);
            }
            field_id = self.tx_buffer.read_var_uint()?;
            type_descriptor = self.tx_buffer.peek_type_descriptor()?;
            if type_descriptor.is_nop() {
                let bytes_skipped = self.tx_buffer.read_nop_pad()?;
                nop_byte_count += bytes_skipped;
                *self.state = ReaderState::Skipping(nop_byte_count);
            } else {
                // `read_value_header` above records offsets/lengths for the value itself, but we still
                // need to record this information for the field ID.
                self.encoded_value.field_id_length = u8::try_from(field_id.size_in_bytes())
                    .map_err(|_e| decoding_error_raw("found a field ID > 255 bytes long"))?;
                self.encoded_value.field_id = Some(RawSymbolToken::SymbolId(field_id.value()));
                break self.read_value_header(type_descriptor)?;
            }
        };
        Ok(stream_item)
    }

    fn read_annotated_value_header(mut self, mut header: Header) -> IonResult<RawStreamItem> {
        // Read the annotations envelope from tx_buffer
        self.read_annotations_envelope(header)?;

        header = self.tx_buffer.peek_type_descriptor()?;
        // Read the value's header from tx_buffer
        let stream_item = self.read_unannotated_value_header(header)?;
        // If we've gotten this far, our EncodedValue has been populated with the necessary offsets
        Ok(stream_item)
    }

    fn read_unannotated_value_header(mut self, mut header: Header) -> IonResult<RawStreamItem> {
        // Skip over any number of NOP regions
        let mut nop_byte_count = 0;
        while header.is_nop() {
            // We're not on a value, but we are at a place where the reader can safely resume
            // reading if necessary.
            let bytes_skipped = self.tx_buffer.read_nop_pad()?;
            nop_byte_count += bytes_skipped;
            // If we don't reach a value header by the end of this method, make a note to discard
            // these NOP bytes before we do our next attempt. We don't want the reader to have to
            // hold NOP bytes in the buffer if we've already processed them.
            *self.state = ReaderState::Skipping(nop_byte_count);
            header = self.tx_buffer.peek_type_descriptor()?;
        }

        // At the top level, check for a `0xE0`, the first byte in an IVM.
        if header.is_ivm_start() {
            return if self.parent.is_none() {
                // It's an IVM
                self.read_ivm()
            } else {
                decoding_error(format!(
                    "found an Ion version marker inside a {:?}",
                    self.parent.unwrap()
                ))
            };
        }

        if self.is_at_end_of_container() {
            return Ok(RawStreamItem::Nothing);
        }

        // Add the header to the encoded value we're constructing
        self.encoded_value.header = header;
        // Record the *absolute* offset of the type descriptor -- its offset from the beginning of
        // the stream.
        self.encoded_value.header_offset =
            self.main_buffer.total_consumed() + self.tx_buffer.total_consumed();
        // Advance beyond the type descriptor
        self.tx_buffer.consume(1);

        let length = self.tx_buffer.read_value_length(header)?;
        self.encoded_value.header_length = u8::try_from(length.size_in_bytes()).map_err(|_e| {
            decoding_error_raw(format!(
                "found a value with a header length field over 255 bytes long"
            ))
        })?;
        self.encoded_value.value_length = length.value();

        *self.state = ReaderState::OnValue(self.encoded_value);
        // If header.ion_type() were None, `read_value_length(...)` would have failed.
        Ok(RawStreamItem::Value(header.ion_type.unwrap()))
    }

    /// Populates the annotations-related offsets in the `EncodedValue` based on the information
    /// read from the annotations envelope. This method does not read the annotations themselves.
    /// Returns the expected length of the annotated value nested inside the envelope.
    fn read_annotations_envelope(&mut self, header: Header) -> IonResult<usize> {
        // Consume the first byte; its contents are already in the `header` parameter.
        self.tx_buffer.consume(1);

        // Read the combined length of the annotations sequence and the value that follows it
        let annotations_and_value_length = match header.length_code {
            length_codes::NULL => 0,
            length_codes::VAR_UINT => {
                // If the 'length' is a VarUInt, read it in and consume those bytes
                self.tx_buffer.read_var_uint()?.value()
            }
            length => length as usize,
        };

        // Read the length of the annotations sequence
        let annotations_length = self.tx_buffer.read_var_uint()?;

        // Validate that neither the annotations sequence is not empty.
        if annotations_length.value() == 0 {
            return decoding_error("found an annotations wrapper with no annotations");
        }

        // Validate that the annotated value is not missing.
        let expected_value_length = annotations_and_value_length
            - annotations_length.size_in_bytes()
            - annotations_length.value();
        if expected_value_length == 0 {
            return decoding_error("found an annotation wrapper with no value");
        }

        // Skip over the annotations sequence itself; the reader will return to it if/when the reader
        // asks to iterate over those symbol IDs.
        self.tx_buffer.consume(annotations_length.value());

        // Record the important offsets/lengths so we can revisit the annotations sequence later.
        self.encoded_value.annotations_header_length =
            u8::try_from(self.tx_buffer.total_consumed()).map_err(|_e| {
                decoding_error_raw("found an annotations header greater than 255 bytes long")
            })?;
        self.encoded_value.annotations_sequence_length = u8::try_from(annotations_length.value())
            .map_err(|_e| {
            decoding_error_raw("found an annotations sequence greater than 255 bytes long")
        })?;

        Ok(expected_value_length)
    }

    fn read_ivm(mut self) -> IonResult<RawStreamItem> {
        let (major, minor) = self.tx_buffer.read_ivm()?;
        if !matches!((major, minor), (1, 0)) {
            return decoding_error(format!("unsupported Ion version {:X}.{:X}", major, minor));
        }
        self.ion_version = (major, minor);
        *self.state = ReaderState::OnIvm;
        return Ok(RawStreamItem::VersionMarker(major, minor));
    }

    fn is_in_struct(&self) -> bool {
        self.parent
            .map(|p| p.kind == ContainerType::Struct)
            .unwrap_or(false)
    }

    /// Returns `true` if the reader is inside a container and has consumed enough bytes to have
    /// reached the end.
    fn is_at_end_of_container(&self) -> bool {
        if let Some(parent) = self.parent {
            if self.main_buffer.total_consumed() + self.tx_buffer.total_consumed()
                >= parent.exclusive_end
            {
                return true;
            }
        }
        return false;
    }
}

#[cfg(test)]
mod tests {
    use crate::binary::non_blocking::raw_binary_reader::RawBinaryBufferReader;
    use crate::text::text_value::IntoAnnotations;
    use crate::{IonError, IonResult};
    use std::fmt::Debug;

    use super::*;

    fn expect_incomplete<T: Debug>(result: IonResult<T>) {
        if let Err(IonError::Incomplete { .. }) = result {
            // do nothing
        } else {
            panic!("expected incomplete, found: {:?}", result)
        }
    }

    fn expect_value(result: IonResult<RawStreamItem>, ion_type: IonType) {
        if let Ok(RawStreamItem::Value(result_ion_type)) = result {
            assert_eq!(result_ion_type, ion_type);
        } else {
            panic!("expected a value, but got: {:?}", result);
        }
    }

    fn expect_annotations<A: AsRef<[u8]>, I: IntoAnnotations>(
        reader: &RawBinaryBufferReader<A>,
        annotations: I,
    ) {
        let expected = annotations.into_annotations();
        let actual = reader.annotations().collect::<Vec<RawSymbolToken>>();
        assert_eq!(actual, expected);
    }

    #[test]
    fn read_complete_ivm() -> IonResult<()> {
        let data = &[0xE0, 1, 0, 0xEA];
        let mut reader = RawBinaryBufferReader::new(data);
        assert_eq!(RawStreamItem::VersionMarker(1, 0), reader.next()?);
        Ok(())
    }

    #[test]
    fn read_incomplete_ivm() -> IonResult<()> {
        let data = vec![0xE0];
        let mut reader = RawBinaryBufferReader::new(data);
        // The buffer doesn't contain an entire item
        expect_incomplete(reader.next());
        // We can call .next() again safely any number of times; the result will be the same
        // as the underlying buffer data hasn't changed.
        expect_incomplete(reader.next());
        expect_incomplete(reader.next());
        // We can append data as it becomes available even if it doesn't produce a complete item.
        reader.append_bytes(&[1, 0]);
        expect_incomplete(reader.next());
        // Finally, when we have enough data to produce an item, a call to next() works as expected.
        reader.append_bytes(&[0xEA]);
        assert_eq!(RawStreamItem::VersionMarker(1, 0), reader.next().unwrap());
        Ok(())
    }

    #[test]
    fn read_int_header() -> IonResult<()> {
        let data = vec![0x21, 0x03];
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::Integer);
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn read_incomplete_int() -> IonResult<()> {
        let data = vec![0x21];
        let mut reader = RawBinaryBufferReader::new(data);
        // We can read the *header* of the int just fine
        expect_value(reader.next(), IonType::Integer);
        // Trying to advance beyond it is a problem.
        expect_incomplete(reader.next());
        // This byte completes the int, but we still don't have another value to move to.
        reader.append_bytes(&[0x03]);
        expect_incomplete(reader.next());
        // Now there's an empty string after the int
        reader.append_bytes(&[0x80]);
        expect_value(reader.next(), IonType::String);
        Ok(())
    }

    #[test]
    fn read_many_ints() -> IonResult<()> {
        let data = vec![
            0x21, 0x01, // 1
            0x21, 0x02, // 2
            0x21, 0x03, // 3
        ];
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::Integer);
        assert_eq!(reader.read_integer()?, Integer::I64(1));
        expect_value(reader.next(), IonType::Integer);
        assert_eq!(reader.read_integer()?, Integer::I64(2));
        expect_value(reader.next(), IonType::Integer);
        assert_eq!(reader.read_integer()?, Integer::I64(3));
        // Nothing else in the buffer
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_floats() -> IonResult<()> {
        let data = vec![
            0x48, 0x40, 0x16, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // 5.5e0
            0x48, 0x40, 0x92, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, // 1.2e3
            0x48, 0xc0, 0x20, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, // -8.125e0
        ];
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::Float);
        assert_eq!(reader.read_f64()?, 5.5f64);
        expect_value(reader.next(), IonType::Float);
        assert_eq!(reader.read_f64()?, 1200f64);
        expect_value(reader.next(), IonType::Float);
        assert_eq!(reader.read_f64()?, -8.125f64);
        // Nothing else in the buffer
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_decimals() -> IonResult<()> {
        let data = vec![
            0x50, // 0.
            0x52, 0xc1, 0x33, // 5.1
            0x52, 0x80, 0xe4, // -100.
            0x52, 0x80, 0x1c, // 28.
        ];
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::Decimal);
        assert_eq!(reader.read_decimal()?, Decimal::new(0, 0));
        expect_value(reader.next(), IonType::Decimal);
        assert_eq!(reader.read_decimal()?, Decimal::new(51, -1));
        expect_value(reader.next(), IonType::Decimal);
        assert_eq!(reader.read_decimal()?, Decimal::new(-1, 2));
        expect_value(reader.next(), IonType::Decimal);
        assert_eq!(reader.read_decimal()?, Decimal::new(28, 0));
        // Nothing else in the buffer
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_timestamps() -> IonResult<()> {
        let data = vec![
            0x63, 0xc0, 0x0f, 0xe6, // 2022T
            0x64, 0xc0, 0x0f, 0xe6, 0x86, // 2022-06T
            0x65, 0xc0, 0x0f, 0xe6, 0x86, 0x92, // 2022-06-18
            0x67, 0xc0, 0x0f, 0xe6, 0x86, 0x92, 0x8b, 0x9e, // 2022-06-18T11:30+00:00
            0x6b, 0x42, 0xac, 0x0f, 0xe6, 0x86, 0x92, 0x90, // 2022-06-18T11:30:51.115-05:00
            0x9e, 0xb3, 0xc3, 0x73,
        ];
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_year(2022).build()?
        );
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_year(2022).with_month(6).build()?
        );
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2022, 6, 18).build()?
        );
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2022, 6, 18)
                .with_hour_and_minute(11, 30)
                .build_at_offset(0)?
        );
        expect_value(reader.next(), IonType::Timestamp);
        assert_eq!(
            reader.read_timestamp()?,
            Timestamp::with_ymd(2022, 6, 18)
                .with_hms(11, 30, 51)
                .with_milliseconds(115)
                .build_at_offset(-5 * 60)?
        );
        // Nothing else in the buffer
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_symbols() -> IonResult<()> {
        let data = vec![
            0x70, // $0
            0x71, 0x01, // $1
            0x71, 0x02, // $2
            0x72, 0x00, 0x03, // inefficiently encoded $3
        ];
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::Symbol);
        assert_eq!(reader.read_symbol_id()?, 0);
        expect_value(reader.next(), IonType::Symbol);
        assert_eq!(reader.read_symbol_id()?, 1);
        expect_value(reader.next(), IonType::Symbol);
        assert_eq!(reader.read_symbol_id()?, 2);
        expect_value(reader.next(), IonType::Symbol);
        assert_eq!(reader.read_symbol_id()?, 3);
        // Nothing else in the buffer
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_strings() -> IonResult<()> {
        let data = vec![
            0x80, // ""
            0x83, 0x66, 0x6f, 0x6f, // "foo"
            0x83, 0x62, 0x61, 0x72, // "bar"
            0x83, 0x62, 0x61, 0x7a, // "baz"
        ];
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::String);
        assert_eq!(reader.read_str()?, "");
        expect_value(reader.next(), IonType::String);
        assert_eq!(reader.read_str()?, "foo");
        expect_value(reader.next(), IonType::String);
        assert_eq!(reader.read_str()?, "bar");
        expect_value(reader.next(), IonType::String);
        assert_eq!(reader.read_str()?, "baz");
        // Nothing else in the buffer
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_clobs() -> IonResult<()> {
        let data = vec![
            0x90, // empty
            0x93, 0x66, 0x6f, 0x6f, // b"foo"
            0x93, 0x62, 0x61, 0x72, // b"bar"
            0x93, 0x62, 0x61, 0x7a, // b"baz"
        ];
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::Clob);
        assert_eq!(reader.read_clob()?, b"");
        expect_value(reader.next(), IonType::Clob);
        assert_eq!(reader.read_clob()?, b"foo");
        expect_value(reader.next(), IonType::Clob);
        assert_eq!(reader.read_clob()?, b"bar");
        expect_value(reader.next(), IonType::Clob);
        assert_eq!(reader.read_clob()?, b"baz");
        // Nothing else in the buffer
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_blobs() -> IonResult<()> {
        let data = vec![
            0xA0, // empty
            0xA3, 0x66, 0x6f, 0x6f, // b"foo"
            0xA3, 0x62, 0x61, 0x72, // b"bar"
            0xA3, 0x62, 0x61, 0x7a, // b"baz"
        ];
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::Blob);
        assert_eq!(reader.read_blob()?, b"");
        expect_value(reader.next(), IonType::Blob);
        assert_eq!(reader.read_blob()?, b"foo");
        expect_value(reader.next(), IonType::Blob);
        assert_eq!(reader.read_blob()?, b"bar");
        expect_value(reader.next(), IonType::Blob);
        assert_eq!(reader.read_blob()?, b"baz");
        // Nothing else in the buffer
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn read_many_annotated_ints() -> IonResult<()> {
        let data = vec![
            0xE4, 0x81, 0x84, 0x21, 0x01, // $4::1
            0xE4, 0x81, 0x85, 0x21, 0x02, // $5::2
            0xE6, 0x83, 0x86, 0x87, 0x88, 0x21, 0x03, // $6::$7::$8::3
        ];
        let mut reader = RawBinaryBufferReader::new(data);

        expect_value(reader.next(), IonType::Integer);
        expect_annotations(&reader, &[4]);

        expect_value(reader.next(), IonType::Integer);
        expect_annotations(&reader, &[5]);

        expect_value(reader.next(), IonType::Integer);
        expect_annotations(&reader, &[6, 7, 8]);
        // Nothing else in the buffer
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn step_into_list() -> IonResult<()> {
        let data = &[
            0xb4, //  [
            0x21, 0x01, //    1,
            0x21, 0x02, //    2 ]
            0x80, //  "" /*empty string*/
        ];

        // === Skip over list ===
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::List);
        expect_value(reader.next(), IonType::String);
        // Nothing else in the buffer
        expect_incomplete(reader.next());

        // === Early step out ===
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::List);
        reader.step_in()?;
        expect_value(reader.next(), IonType::Integer);
        reader.step_out()?; // Skips second int in list
        expect_value(reader.next(), IonType::String);
        // Nothing else in the buffer
        expect_incomplete(reader.next());

        // === Visit all values ===
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::List);
        reader.step_in()?;
        expect_value(reader.next(), IonType::Integer);
        expect_value(reader.next(), IonType::Integer);
        reader.step_out()?;
        // There's an empty string after the list
        expect_value(reader.next(), IonType::String);
        // Nothing else in the buffer
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn step_into_empty_list() -> IonResult<()> {
        let data = &[0xB0, 0x80]; // Empty list, empty string
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::List);
        reader.step_in()?;
        // Empty list, calling next() returns Nothing
        assert_eq!(reader.next().unwrap(), RawStreamItem::Nothing);
        reader.step_out()?;
        expect_value(reader.next(), IonType::String);
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn step_into_empty_list_with_nop_padding() -> IonResult<()> {
        let data = &[0xB3, 0x00, 0x00, 0x00, 0x80]; // Empty list, empty string
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::List);
        reader.step_in()?;
        // Empty list, calling next() returns Nothing
        assert_eq!(reader.next().unwrap(), RawStreamItem::Nothing);
        reader.step_out()?;
        expect_value(reader.next(), IonType::String);
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn step_into_empty_struct() -> IonResult<()> {
        let data = &[0xD0, 0x80]; // Empty struct, empty string
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::Struct);
        reader.step_in()?;
        // Empty list, calling next() returns Nothing
        assert_eq!(reader.next().unwrap(), RawStreamItem::Nothing);
        reader.step_out()?;
        expect_value(reader.next(), IonType::String);
        expect_incomplete(reader.next());
        Ok(())
    }

    #[test]
    fn step_into_empty_struct_with_nop_padding() -> IonResult<()> {
        let data = &[
            0xD4, 0x80, 0x00, // $0: NOP,
            0x80, 0x00, // $0: NOP,
            0x80,
        ]; // Empty string
        let mut reader = RawBinaryBufferReader::new(data);
        expect_value(reader.next(), IonType::Struct);
        reader.step_in()?;
        // Empty list, calling next() returns Nothing
        assert_eq!(reader.next().unwrap(), RawStreamItem::Nothing);
        reader.step_out()?;
        expect_value(reader.next(), IonType::String);
        expect_incomplete(reader.next());
        Ok(())
    }

    // TODO: Reshape IonError variants so you don't have to match on structs
}
