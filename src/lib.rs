#![allow(dead_code)]
#![deny(rustdoc::broken_intra_doc_links)]

pub mod result;

pub mod binary;
pub mod data_source;
pub mod raw_reader;
pub mod text;
pub mod types;
pub mod value;

pub mod constants;
pub mod ion_eq;
mod raw_symbol_token;
mod raw_symbol_token_ref;
mod reader;
mod stream_reader;
mod symbol;
mod symbol_table;
mod system_reader;
mod writer;

pub use data_source::IonDataSource;
pub use raw_symbol_token::RawSymbolToken;
pub use raw_symbol_token_ref::RawSymbolTokenRef;

pub use symbol::Symbol;
pub use symbol_table::SymbolTable;

pub use types::decimal::Decimal;
pub use types::integer::Integer;
pub use types::timestamp::Timestamp;
pub use types::IonType;

pub use binary::binary_writer::{BinaryWriter, BinaryWriterBuilder};
pub use text::text_writer::{TextWriter, TextWriterBuilder};
pub use writer::IonWriter;

pub use binary::raw_binary_reader::RawBinaryReader;
pub use binary::raw_binary_writer::RawBinaryWriter;
pub use raw_reader::{RawReader, RawStreamItem};
pub use reader::StreamItem;
pub use reader::{Reader, ReaderBuilder, UserReader};
pub use stream_reader::IonReader;
pub use system_reader::{SystemReader, SystemStreamItem};
pub use text::raw_text_reader::RawTextReader;
pub use text::raw_text_writer::RawTextWriter;
pub use text::raw_text_writer::RawTextWriterBuilder;

pub use result::IonError;
pub use result::IonResult;

/// Re-exports of third party dependencies that are part of our public API.
///
/// See also: <https://github.com/amzn/ion-rust/issues/302>
pub mod external {
    pub use bigdecimal;
}
