use crate::{
    binary::{constants::v1_0::length_codes, nibbles::nibbles_from_byte, IonTypeCode},
    result::IonResult,
    types::IonType,
};

pub(crate) const ION_1_0_HEADER_CACHE: &[Header; 256] = &init_header_cache();

/// Contains all of the information that can be extracted from the one-octet type descriptor
/// found at the beginning of each value in a binary Ion stream.
/// For more information, consult the
/// [Typed Value Formats](http://amzn.github.io/ion-docs/docs/binary.html#typed-value-formats)
/// section of the binary Ion spec.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct Header {
    pub ion_type_code: IonTypeCode,
    pub ion_type: Option<IonType>,
    pub length_code: u8,
}

const DEFAULT_HEADER: Header = Header {
    ion_type_code: IonTypeCode::NullOrNop,
    ion_type: None,
    length_code: 0,
};

pub(crate) const fn init_header_cache() -> [Header; 256] {
    let mut jump_table = [DEFAULT_HEADER; 256];
    let mut index: usize = 0;
    while index < 256 {
        let byte = index as u8;
        jump_table[index] = Header::from_byte(byte);
        index += 1;
    }
    jump_table
}

impl Header {
    /// Attempts to parse the provided byte. If the type code is unrecognized or the
    /// type code + length code combination is illegal, an error will be returned.
    pub const fn from_byte(byte: u8) -> Header {
        let (type_code, length_code) = nibbles_from_byte(byte);
        use IonTypeCode::*;
        let ion_type_code = match type_code {
            0 => NullOrNop,
            1 => Boolean,
            2 => PositiveInteger,
            3 => NegativeInteger,
            4 => Float,
            5 => Decimal,
            6 => Timestamp,
            7 => Symbol,
            8 => String,
            9 => Clob,
            10 => Blob,
            11 => List,
            12 => SExpression,
            13 => Struct,
            14 => AnnotationOrIvm,
            15 => Reserved,
            _ => panic!("type code was larger than a nibble"),
        };
        let ion_type = match ion_type_code {
            NullOrNop => None,
            Boolean => Some(IonType::Boolean),
            PositiveInteger => Some(IonType::Integer),
            NegativeInteger => Some(IonType::Integer),
            Float => Some(IonType::Float),
            Decimal => Some(IonType::Decimal),
            Timestamp => Some(IonType::Timestamp),
            Symbol => Some(IonType::Symbol),
            String => Some(IonType::String),
            Clob => Some(IonType::Clob),
            Blob => Some(IonType::Blob),
            List => Some(IonType::List),
            SExpression => Some(IonType::SExpression),
            Struct => Some(IonType::Struct),
            AnnotationOrIvm => None,
            Reserved => None,
        };
        Header {
            ion_type,
            ion_type_code,
            length_code,
        }
    }

    pub fn is_null(&self) -> bool {
        self.ion_type.is_some() && self.length_code == length_codes::NULL
    }

    pub fn is_nop(&self) -> bool {
        self.ion_type_code == IonTypeCode::NullOrNop && self.length_code != length_codes::NULL
    }

    pub fn is_ivm_start(&self) -> bool {
        self.ion_type_code == IonTypeCode::AnnotationOrIvm && self.length_code == 0
    }

    pub fn is_annotation_wrapper(&self) -> bool {
        self.ion_type_code == IonTypeCode::AnnotationOrIvm && self.length_code > 0
    }
}

/// Parses all possible values of a single byte and stores them in a newly allocated Vec.
/// This Vec may be used as a jump table to avoid re-calculating the meaning of the same byte
/// value repeatedly.
/// It is expected that the jump table will be referenced when a reader attempts to begin reading
/// the next value from its input data. This calling code must handle the end-of-file case,
/// IO errors, and decoding errors. Each value in the table is stored as an
/// IonResult<Option<IonValueHeader>> so that in the even that another value is available and
/// no IO errors occur, the value from the jump table can be returned as-is with no transformations
/// required.
/// All values stored in the table are either an `Err(IonError::DecodingError)` or an
/// `Ok(Some(IonValueHeader))`.
// TODO: Define the jump table as a static constant at compile time to avoid recalculating it.
// https://github.com/amzn/ion-rust/issues/4
pub(crate) fn create_header_byte_jump_table() -> Vec<IonResult<Option<Header>>> {
    let mut header_jump_table = Vec::with_capacity(256);
    for byte_value in 0..=255 {
        // let entry = match Header::from_byte(byte_value) {
        //     Ok(header) => Ok(Some(header)),
        //     Err(error) => Err(error),
        // };
        let entry = Header::from_byte(byte_value);
        header_jump_table.push(Ok(Some(entry)));
    }
    header_jump_table
}
