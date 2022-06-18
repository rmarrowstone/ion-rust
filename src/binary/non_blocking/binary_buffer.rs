use crate::binary::constants::v1_0::{length_codes, IVM};
use crate::binary::header::{Header, ION_1_0_HEADER_CACHE};
use crate::binary::int::DecodedInt;
use crate::binary::uint::DecodedUInt;
use crate::binary::var_int::VarInt;
use crate::binary::var_uint::VarUInt;
use crate::result::{decoding_error, incomplete_data_error, incomplete_data_error_raw};
use crate::types::integer::UInteger;
use crate::{Integer, IonResult, IonType};
use num_bigint::{BigInt, BigUint, Sign};
use std::io::Read;
use std::mem;

// This limit is used for stack-allocating buffer space to encode/decode UInts.
const UINT_STACK_BUFFER_SIZE: usize = 16;
// This number was chosen somewhat arbitrarily and could be lifted if a use case demands it.
const MAX_UINT_SIZE_IN_BYTES: usize = 2048;

// This limit is used for stack-allocating buffer space to encode/decode Ints.
const INT_STACK_BUFFER_SIZE: usize = 16;
// This number was chosen somewhat arbitrarily and could be lifted if a use case demands it.
const MAX_INT_SIZE_IN_BYTES: usize = 2048;

#[derive(Debug, PartialEq)]
pub(crate) struct BinaryBuffer<A: AsRef<[u8]>> {
    data: A,
    start: usize,
    end: usize,
    total_consumed: usize,
}

impl<A: AsRef<[u8]>> BinaryBuffer<A> {
    #[inline]
    pub fn new(data: A) -> BinaryBuffer<A> {
        let end = data.as_ref().len();
        BinaryBuffer {
            data,
            start: 0,
            end,
            total_consumed: 0,
        }
    }

    pub fn slice(&self) -> BinaryBuffer<&A> {
        BinaryBuffer {
            data: &self.data,
            start: self.start,
            end: self.end,
            total_consumed: 0,
        }
    }

    pub fn bytes(&self) -> &[u8] {
        &self.data.as_ref()[self.start..self.end]
    }

    pub fn total_consumed(&self) -> usize {
        self.total_consumed
    }

    pub fn remaining(&self) -> usize {
        self.bytes().len()
    }

    pub fn is_empty(&self) -> bool {
        self.remaining() == 0
    }

    pub fn peek_next_byte(&self) -> Option<u8> {
        if self.is_empty() {
            return None;
        }
        Some(self.bytes()[0])
    }

    pub fn peek_n_bytes(&self, n: usize) -> Option<&[u8]> {
        if self.bytes().len() < n {
            return None;
        }
        Some(&self.bytes()[0..n])
    }

    /// After data has been inspected using the `peek` methods, those bytes can be marked as read
    /// by calling the consume method.
    pub fn consume(&mut self, num_bytes_to_consume: usize) {
        if num_bytes_to_consume > self.remaining() {
            panic!(
                "attempted to consume {} bytes when only {} remain",
                num_bytes_to_consume,
                self.remaining()
            )
        }
        self.start += num_bytes_to_consume;
        self.total_consumed += num_bytes_to_consume;
    }

    pub fn peek_type_descriptor(&self) -> IonResult<Header> {
        let next_byte = self
            .peek_next_byte()
            .ok_or_else(|| incomplete_data_error_raw("a type descriptor", self.total_consumed()))?;

        Ok(ION_1_0_HEADER_CACHE[next_byte as usize])
    }

    pub fn read_ivm(&mut self) -> IonResult<(u8, u8)> {
        let bytes = self
            .peek_n_bytes(IVM.len())
            .ok_or_else(|| incomplete_data_error_raw("a UInt", self.total_consumed()))?;

        match bytes {
            [0xE0, major, minor, 0xEA] => {
                let version = (*major, *minor);
                self.consume(IVM.len());
                Ok(version)
            }
            invalid_ivm => decoding_error(format!("invalid IVM: {:?}", invalid_ivm)),
        }
    }

    pub fn read_var_uint(&mut self) -> IonResult<VarUInt> {
        const BITS_PER_ENCODED_BYTE: usize = 7;
        const STORAGE_SIZE_IN_BITS: usize = mem::size_of::<usize>() * 8;
        const MAX_ENCODED_SIZE_IN_BYTES: usize = STORAGE_SIZE_IN_BITS / BITS_PER_ENCODED_BYTE;

        const LOWER_7_BITMASK: u8 = 0b0111_1111;
        const HIGHEST_BIT_VALUE: u8 = 0b1000_0000;

        let mut magnitude: usize = 0;
        let mut encoded_size_in_bytes = 0;
        // Whether we found the terminating byte in this buffer.
        let mut terminated = false;

        for byte in self.bytes().iter().copied() {
            let lower_seven = (LOWER_7_BITMASK & byte) as usize;
            magnitude <<= 7; // Shifts 0 to 0 in the first iteration
            magnitude |= lower_seven;
            encoded_size_in_bytes += 1;
            // If the highest bit is one, that was the final byte
            if byte >= HIGHEST_BIT_VALUE {
                terminated = true;
                break;
            }
        }

        if !terminated {
            return incomplete_data_error(
                "a VarUInt",
                self.total_consumed() + encoded_size_in_bytes,
            );
        }

        // Prevent overflow by checking that the VarUInt was not too large to safely fit in the
        // data type being used to house the decoded value.
        //
        // This approach has two drawbacks:
        // * When using a u64, we only allow up to 63 bits of encoded magnitude data.
        // * It will return an error for inefficiently-encoded small values that use more bytes
        //   than required. (e.g. A 10-byte encoding of the number 0 will be rejected.)
        //
        // However, reading VarUInt values is a very hot code path for reading binary Ion. This
        // compromise allows us to prevent overflows for the cost of a single branch per VarUInt
        // rather than performing extra bookkeeping logic on a per-byte basis.
        if encoded_size_in_bytes > MAX_ENCODED_SIZE_IN_BYTES {
            return decoding_error(format!(
                "Found a {}-byte VarUInt. Max supported size is {} bytes.",
                encoded_size_in_bytes, MAX_ENCODED_SIZE_IN_BYTES
            ));
        }

        self.consume(encoded_size_in_bytes);
        Ok(VarUInt::new(magnitude, encoded_size_in_bytes))
    }

    pub fn read_var_int(&mut self) -> IonResult<VarInt> {
        const BITS_PER_ENCODED_BYTE: usize = 7;
        const STORAGE_SIZE_IN_BITS: usize = mem::size_of::<i64>() * 8;
        const MAX_ENCODED_SIZE_IN_BYTES: usize = STORAGE_SIZE_IN_BITS / BITS_PER_ENCODED_BYTE;

        const LOWER_6_BITMASK: u8 = 0b0011_1111;
        const LOWER_7_BITMASK: u8 = 0b0111_1111;
        const HIGHEST_BIT_VALUE: u8 = 0b1000_0000;

        const BITS_PER_BYTE: usize = 8;
        const BITS_PER_U64: usize = mem::size_of::<u64>() * BITS_PER_BYTE;

        // Unlike VarUInt's encoding, the first byte in a VarInt is a special case because
        // bit #6 (0-indexed, from the right) indicates whether the value is positive (0) or
        // negative (1).

        if self.is_empty() {
            return incomplete_data_error("a VarInt", self.total_consumed());
        }
        let first_byte: u8 = self.peek_next_byte().unwrap();
        let no_more_bytes: bool = first_byte >= 0b1000_0000; // If the first bit is 1, we're done.
        let is_positive: bool = (first_byte & 0b0100_0000) == 0;
        let sign: i64 = if is_positive { 1 } else { -1 };
        let mut magnitude = (first_byte & 0b0011_1111) as i64;

        if no_more_bytes {
            self.consume(1);
            return Ok(VarInt::new(magnitude * sign, !is_positive, 1));
        }

        let mut encoded_size_in_bytes = 1;
        // Whether we found the terminating byte in this buffer.
        let mut terminated = false;

        for byte in self.bytes()[1..].iter().copied() {
            let lower_seven = (0b0111_1111 & byte) as i64;
            magnitude <<= 7;
            magnitude |= lower_seven;
            encoded_size_in_bytes += 1;
            if byte >= 0b1000_0000 {
                terminated = true;
                break;
            }
        }

        if !terminated {
            return incomplete_data_error(
                "a VarInt",
                self.total_consumed() + encoded_size_in_bytes,
            );
        }

        if encoded_size_in_bytes > MAX_ENCODED_SIZE_IN_BYTES {
            return decoding_error(format!(
                "Found a {}-byte VarInt. Max supported size is {} bytes.",
                encoded_size_in_bytes, MAX_ENCODED_SIZE_IN_BYTES
            ));
        }

        self.consume(encoded_size_in_bytes);
        Ok(VarInt::new(
            magnitude * sign,
            !is_positive,
            encoded_size_in_bytes,
        ))
    }

    pub fn read_uint(&mut self, length: usize) -> IonResult<DecodedUInt> {
        if length > MAX_UINT_SIZE_IN_BYTES {
            return decoding_error(format!(
                "Found a {}-byte UInt. Max supported size is {} bytes.",
                length, MAX_UINT_SIZE_IN_BYTES
            ));
        }

        let uint_bytes = self
            .peek_n_bytes(length)
            .ok_or_else(|| incomplete_data_error_raw("a UInt", self.total_consumed()))?;

        let value = if length <= mem::size_of::<u64>() {
            // The UInt is small enough to fit in a u64.
            // TODO: u64::from_be_bytes(...) is now available. It requires a [u8; 8] (not a &[u8]).
            let mut magnitude: u64 = 0;
            for &byte in uint_bytes {
                let byte = u64::from(byte);
                magnitude <<= 8;
                magnitude |= byte;
            }
            UInteger::U64(magnitude)
        } else {
            // The UInt is too large to fit in a u64; read it as a BigUInt instead
            let magnitude = BigUint::from_bytes_be(uint_bytes);
            UInteger::BigUInt(magnitude)
        };

        self.consume(length);
        Ok(DecodedUInt::new(value, length))
    }

    pub fn read_int(&mut self, length: usize) -> IonResult<DecodedInt> {
        if length == 0 {
            return Ok(DecodedInt::new(Integer::I64(0), false, 0));
        } else if length > MAX_INT_SIZE_IN_BYTES {
            return decoding_error(format!(
                "Found a {}-byte Int. Max supported size is {} bytes.",
                length, MAX_INT_SIZE_IN_BYTES
            ));
        }

        let int_bytes = self.peek_n_bytes(length).ok_or_else(|| {
            incomplete_data_error_raw("an Int encoding primitive", self.total_consumed())
        })?;

        let mut is_negative: bool = false;

        let value = if length <= mem::size_of::<i64>() {
            // This Int will fit in an i64.
            let first_byte: i64 = i64::from(int_bytes[0]);
            let sign: i64 = if first_byte & 0b1000_0000 == 0 {
                1
            } else {
                is_negative = true;
                -1
            };
            let mut magnitude: i64 = first_byte & 0b0111_1111;
            for &byte in &int_bytes[1..] {
                let byte = i64::from(byte);
                magnitude <<= 8;
                magnitude |= byte;
            }
            Integer::I64(sign * magnitude)
        } else {
            // This Int is too big for an i64, we'll need to use a BigInt
            let value = if int_bytes[0] & 0b1000_0000 == 0 {
                BigInt::from_bytes_be(Sign::Plus, int_bytes)
            } else {
                is_negative = true;
                // The leading sign bit is the only part of the input that can't be considered
                // unsigned, big-endian integer bytes. We need to make our own copy of the input
                // so we can flip that bit back to a zero before calling `from_bytes_be`.
                let mut owned_int_bytes = Vec::from(int_bytes);
                owned_int_bytes[0] &= 0b0111_1111;
                BigInt::from_bytes_be(Sign::Minus, owned_int_bytes.as_slice())
            };

            Integer::BigInt(value)
        };
        self.consume(length);
        Ok(DecodedInt::new(value, is_negative, length))
    }

    pub fn read_nop_pad(&mut self) -> IonResult<usize> {
        let type_descriptor = self.peek_type_descriptor()?;
        // Advance beyond the type descriptor
        self.consume(1);
        // If the type descriptor says we should skip more bytes, skip them.
        let length = self.read_standard_length(type_descriptor)?;
        self.consume(length.value());
        Ok(1 + length.size_in_bytes() + length.value())
    }

    pub fn read_value_length(&mut self, header: Header) -> IonResult<VarUInt> {
        let ion_type = match header.ion_type {
            Some(ion_type) => ion_type,
            None => {
                return decoding_error(format!(
                    "found non-value type descriptor {:?} in value position",
                    header
                ))
            }
        };

        use IonType::*;
        let length: VarUInt = match ion_type {
            Null | Boolean => VarUInt::new(0, 0),
            Integer | Decimal | String | Symbol | List | SExpression | Clob | Blob => {
                self.read_standard_length(header)?
            }
            Timestamp => {
                let length = self.read_standard_length(header)?;
                if length.value() <= 1 && !header.is_null() {
                    return decoding_error(
                        "found a non-null timestamp (typecode=6) with a length <= 1",
                    );
                }
                length
            }
            Float => self.read_float_length(header)?,
            Struct => self.read_struct_length(header)?,
        };
        Ok(length)
    }

    // The interpretation of a type descriptor's `L` nibble (length) used by most Ion types.
    pub fn read_standard_length(&mut self, header: Header) -> IonResult<VarUInt> {
        let length = match header.length_code {
            length_codes::NULL => VarUInt::new(0, 0),
            length_codes::VAR_UINT => self.read_var_uint()?,
            magnitude => VarUInt::new(magnitude as usize, 0),
        };

        Ok(length)
    }

    fn read_float_length(&mut self, header: Header) -> IonResult<VarUInt> {
        let length = match header.length_code {
            0 => 0,
            4 => 4,
            8 => 8,
            length_codes::NULL => 0,
            _ => {
                return decoding_error(format!(
                    "found a float value with an illegal length: {}",
                    header.length_code
                ))
            }
        };
        Ok(VarUInt::new(length, 0))
    }

    fn read_struct_length(&mut self, header: Header) -> IonResult<VarUInt> {
        let length = match header.length_code {
            length_codes::NULL => VarUInt::new(0, 0),
            // If the length code is `1`, it indicates an ordered struct. This is a special case
            // of struct; it cannot be empty, and its fields must appear in ascending order of
            // symbol ID. For the time being, the binary reader doesn't implement any special
            // handling for it.
            1 => {
                let length = self.read_var_uint()?;
                if length.value() == 0 {
                    return decoding_error("found an empty ordered struct");
                }
                length
            }
            length_codes::VAR_UINT => self.read_var_uint()?,
            magnitude => VarUInt::new(magnitude as usize, 0),
        };

        Ok(length)
    }
}

impl BinaryBuffer<Vec<u8>> {
    fn restack(&mut self) {
        // Re-stack the buffer by moving any remaining bytes back to the front of the Vec
        let remaining = self.remaining();
        self.data.copy_within(self.start..self.end, 0);
        self.start = 0;
        self.end = remaining;
        self.data.truncate(remaining);
    }

    pub fn append_bytes(&mut self, bytes: &[u8]) {
        self.restack();
        self.data.extend_from_slice(bytes);
        self.end += bytes.len();
    }

    fn reserve_capacity(&mut self, length: usize) {
        // TODO: More sophisticated analysis to avoid potentially reallocating multiple times per call.
        //       For now, it is unlikely that this would happen often.
        let capacity = self.data.len() - self.end;
        if capacity < length {
            for _ in 0..(length - capacity) {
                self.data.push(0);
            }
        }
    }

    pub fn read_from<R: Read>(&mut self, mut source: R, length: usize) -> IonResult<usize> {
        self.restack();
        self.reserve_capacity(length);
        let read_buffer = &mut self.data.as_mut_slice()[self.end..length];
        let bytes_read = source.read(read_buffer)?;
        self.end += bytes_read;
        Ok(bytes_read)
    }
}

impl<A: AsRef<[u8]>> From<A> for BinaryBuffer<A> {
    fn from(data: A) -> Self {
        let end = data.as_ref().len();
        BinaryBuffer {
            data,
            start: 0,
            end,
            total_consumed: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::IonError;
    use num_traits::Num;

    fn input_test<I: AsRef<[u8]> + Into<BinaryBuffer<I>>>(input: I) {
        let mut input = input.into();
        // We can peek at the first byte...
        assert_eq!(input.peek_next_byte(), Some(b'f'));
        // ...without modifying the input. Looking at the next 3 bytes still includes 'f'.
        assert_eq!(input.peek_n_bytes(3), Some("foo".as_bytes()));
        // Advancing the cursor by 1...
        input.consume(1);
        // ...causes next_byte() to return 'o'.
        assert_eq!(input.peek_next_byte(), Some(b'o'));
        input.consume(1);
        assert_eq!(input.peek_next_byte(), Some(b'o'));
        input.consume(1);
        assert_eq!(input.peek_n_bytes(2), Some(" b".as_bytes()));
        assert_eq!(input.peek_n_bytes(6), Some(" bar b".as_bytes()));
    }

    #[test]
    fn string_test() {
        input_test(String::from("foo bar baz"));
    }

    #[test]
    fn slice_test() {
        input_test("foo bar baz".as_bytes());
    }

    #[test]
    fn vec_test() {
        input_test(Vec::from("foo bar baz".as_bytes()));
    }

    #[test]
    fn read_var_uint() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001]);
        let var_uint = buffer.read_var_uint()?;
        assert_eq!(3, var_uint.size_in_bytes());
        assert_eq!(1_984_385, var_uint.value());
        Ok(())
    }

    #[test]
    fn read_var_uint_zero() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1000_0000]);
        let var_uint = buffer.read_var_uint()?;
        assert_eq!(var_uint.size_in_bytes(), 1);
        assert_eq!(var_uint.value(), 0);
        Ok(())
    }

    #[test]
    fn read_var_uint_two_bytes_max_value() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let var_uint = buffer.read_var_uint()?;
        assert_eq!(var_uint.size_in_bytes(), 2);
        assert_eq!(var_uint.value(), 16_383);
        Ok(())
    }

    #[test]
    fn read_incomplete_var_uint() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1001, 0b0000_1111]);
        match buffer.read_var_uint() {
            Err(IonError::Incomplete { .. }) => Ok(()),
            other => panic!("expected IonError::Incomplete, but found: {:?}", other),
        }
    }

    #[test]
    fn read_var_uint_overflow_detection() {
        let mut buffer = BinaryBuffer::new(&[
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b1111_1111,
        ]);
        buffer
            .read_var_uint()
            .expect_err("This should have failed due to overflow.");
    }

    #[test]
    fn read_var_int_zero() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1000_0000]);
        let var_int = buffer.read_var_int()?;
        assert_eq!(var_int.size_in_bytes(), 1);
        assert_eq!(var_int.value(), 0);
        Ok(())
    }

    #[test]
    fn read_negative_var_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1001, 0b0000_1111, 0b1000_0001]);
        let var_int = buffer.read_var_int()?;
        assert_eq!(var_int.size_in_bytes(), 3);
        assert_eq!(var_int.value(), -935_809);
        Ok(())
    }

    #[test]
    fn read_positive_var_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0011_1001, 0b0000_1111, 0b1000_0001]);
        let var_int = buffer.read_var_int()?;
        assert_eq!(var_int.size_in_bytes(), 3);
        assert_eq!(var_int.value(), 935_809);
        Ok(())
    }

    #[test]
    fn read_var_int_two_byte_min() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let var_int = buffer.read_var_int()?;
        assert_eq!(var_int.size_in_bytes(), 2);
        assert_eq!(var_int.value(), -8_191);
        Ok(())
    }

    #[test]
    fn read_var_int_two_byte_max() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0011_1111, 0b1111_1111]);
        let var_int = buffer.read_var_int()?;
        assert_eq!(var_int.size_in_bytes(), 2);
        assert_eq!(var_int.value(), 8_191);
        Ok(())
    }

    #[test]
    fn read_var_int_overflow_detection() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b0111_1111,
            0b1111_1111,
        ]);
        buffer
            .read_var_int()
            .expect_err("This should have failed due to overflow.");
        Ok(())
    }

    #[test]
    fn read_one_byte_uint() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1000_0000]);
        let var_int = buffer.read_uint(buffer.remaining())?;
        assert_eq!(var_int.size_in_bytes(), 1);
        assert_eq!(var_int.value(), &UInteger::U64(128));
        Ok(())
    }

    #[test]
    fn read_two_byte_uint() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let var_int = buffer.read_uint(buffer.remaining())?;
        assert_eq!(var_int.size_in_bytes(), 2);
        assert_eq!(var_int.value(), &UInteger::U64(32_767));
        Ok(())
    }

    #[test]
    fn read_three_byte_uint() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0011_1100, 0b1000_0111, 0b1000_0001]);
        let var_int = buffer.read_uint(buffer.remaining())?;
        assert_eq!(var_int.size_in_bytes(), 3);
        assert_eq!(var_int.value(), &UInteger::U64(3_966_849));
        Ok(())
    }

    #[test]
    fn test_read_ten_byte_uint() -> IonResult<()> {
        let data = vec![0xFFu8; 10];
        let mut buffer = BinaryBuffer::new(data);
        let uint = buffer.read_uint(buffer.remaining())?;
        assert_eq!(uint.size_in_bytes(), 10);
        assert_eq!(
            uint.value(),
            &UInteger::BigUInt(BigUint::from_str_radix("ffffffffffffffffffff", 16).unwrap())
        );
        Ok(())
    }

    #[test]
    fn test_read_uint_too_large() {
        let mut buffer = Vec::with_capacity(MAX_UINT_SIZE_IN_BYTES + 1);
        for _ in 0..(MAX_UINT_SIZE_IN_BYTES + 1) {
            buffer.push(1);
        }
        let mut buffer = BinaryBuffer::new(buffer);
        let _uint = buffer
            .read_uint(buffer.remaining())
            .expect_err("This exceeded the configured max UInt size.");
    }

    #[test]
    fn read_int_negative_zero() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1000_0000]); // Negative zero
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 1);
        assert_eq!(int.value(), &Integer::I64(0));
        assert!(int.is_negative_zero());
        Ok(())
    }

    #[test]
    fn read_int_positive_zero() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0000_0000]); // Negative zero
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 1);
        assert_eq!(int.value(), &Integer::I64(0));
        assert!(!int.is_negative_zero());
        Ok(())
    }

    #[test]
    fn read_int_length_zero() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[]); // Negative zero
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 0);
        assert_eq!(int.value(), &Integer::I64(0));
        assert!(!int.is_negative_zero());
        Ok(())
    }

    #[test]
    fn read_two_byte_negative_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1111_1111, 0b1111_1111]);
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 2);
        assert_eq!(int.value(), &Integer::I64(-32_767));
        Ok(())
    }

    #[test]
    fn read_two_byte_positive_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0111_1111, 0b1111_1111]);
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 2);
        assert_eq!(int.value(), &Integer::I64(32_767));
        Ok(())
    }

    #[test]
    fn read_three_byte_negative_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b1011_1100, 0b1000_0111, 0b1000_0001]);
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 3);
        assert_eq!(int.value(), &Integer::I64(-3_966_849));
        Ok(())
    }

    #[test]
    fn read_three_byte_positive_int() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(&[0b0011_1100, 0b1000_0111, 0b1000_0001]);
        let int = buffer.read_int(buffer.remaining())?;
        assert_eq!(int.size_in_bytes(), 3);
        assert_eq!(int.value(), &Integer::I64(3_966_849));
        Ok(())
    }

    #[test]
    fn read_int_overflow() -> IonResult<()> {
        let mut buffer = BinaryBuffer::new(vec![1; MAX_INT_SIZE_IN_BYTES + 1]); // Negative zero
        buffer
            .read_int(buffer.remaining())
            .expect_err("This exceeded the configured max Int size.");
        Ok(())
    }
}
