impl ops::Deref for SudoString {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        let num_bytes = self.inner.len();
        &self.inner[..num_bytes - NULL_BYTE_UTF8_LEN]
    }
}
