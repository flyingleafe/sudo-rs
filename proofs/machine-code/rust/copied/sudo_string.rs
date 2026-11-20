const NULL_BYTE: char = '\0';
const NULL_BYTE_UTF8_LEN: usize = NULL_BYTE.len_utf8();

/// A UTF-8 encoded string with no interior null bytes
///
/// This type can be converted into a C (null-terminated) string at no cost
#[derive(Clone, PartialEq, Eq)]
pub struct SudoString {
    inner: String,
}
