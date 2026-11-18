// -*- mode: Bluespec; -*-
// Concrete implementations (feature sets) and one mutant per historical bug.
// Run any of these modules with `--main=<module>`.

// Original C sudo (1.9.x feature set, all known fixes applied).
module ogsudo {
  import sudo(
    IMPL = { hostOpt: true, chrootOpt: true, mailer: true, timeWindows: true, sudoedit: true, askpass: true },
    BUGS = Set()
  ).* from "./sudo"
}

// sudo-rs: no `-h host`, no `-R`/CHROOT, no mailer, no NOTBEFORE/NOTAFTER.
module sudors {
  import sudo(
    IMPL = { hostOpt: false, chrootOpt: false, mailer: false, timeWindows: false, sudoedit: true, askpass: true },
    BUGS = Set()
  ).* from "./sudo"
}

module mut_cve_2026_35535 {
  import sudo(
    IMPL = { hostOpt: true, chrootOpt: true, mailer: true, timeWindows: true, sudoedit: true, askpass: true },
    BUGS = Set("CVE-2026-35535")
  ).* from "./sudo"
}

module mut_cve_2025_32463 {
  import sudo(
    IMPL = { hostOpt: true, chrootOpt: true, mailer: true, timeWindows: true, sudoedit: true, askpass: true },
    BUGS = Set("CVE-2025-32463")
  ).* from "./sudo"
}

module mut_cve_2025_32462 {
  import sudo(
    IMPL = { hostOpt: true, chrootOpt: true, mailer: true, timeWindows: true, sudoedit: true, askpass: true },
    BUGS = Set("CVE-2025-32462")
  ).* from "./sudo"
}

module mut_cve_2019_14287 {
  import sudo(
    IMPL = { hostOpt: true, chrootOpt: true, mailer: true, timeWindows: true, sudoedit: true, askpass: true },
    BUGS = Set("CVE-2019-14287")
  ).* from "./sudo"
}

module mut_cve_2026_96512 {
  import sudo(
    IMPL = { hostOpt: true, chrootOpt: true, mailer: true, timeWindows: true, sudoedit: true, askpass: true },
    BUGS = Set("CVE-2026-96512")
  ).* from "./sudo"
}

module mut_cve_2023_22809 {
  import sudo(
    IMPL = { hostOpt: true, chrootOpt: true, mailer: true, timeWindows: true, sudoedit: true, askpass: true },
    BUGS = Set("CVE-2023-22809")
  ).* from "./sudo"
}

module mut_cve_2025_64517 {
  import sudo(
    IMPL = { hostOpt: false, chrootOpt: false, mailer: false, timeWindows: false, sudoedit: true, askpass: true },
    BUGS = Set("CVE-2025-64517")
  ).* from "./sudo"
}

module mut_cve_2023_42456 {
  import sudo(
    IMPL = { hostOpt: false, chrootOpt: false, mailer: false, timeWindows: false, sudoedit: true, askpass: true },
    BUGS = Set("CVE-2023-42456")
  ).* from "./sudo"
}

// Not a CVE: a /proc/self/stat parser that splits on spaces lets the
// invoker's process name pick the session id (sudo-rs parses after the last
// ')' and is not affected).
module mut_proc_stat_split {
  import sudo(
    IMPL = { hostOpt: false, chrootOpt: false, mailer: false, timeWindows: false, sudoedit: true, askpass: true },
    BUGS = Set("PROC-STAT-SPLIT")
  ).* from "./sudo"
}
