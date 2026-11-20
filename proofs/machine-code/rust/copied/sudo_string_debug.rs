impl fmt::Debug for SudoString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s: &str = self;
        fmt::Debug::fmt(s, f)
    }
}
