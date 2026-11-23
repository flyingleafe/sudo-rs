# Extract libtest outcomes only from complete runs. A pair of empty logs, or two
# runs killed at the same point, is not evidence of identical behavior.
/^running [0-9]+ tests?$/ {
  if (running) bad = 1
  running = 1; planned = $2; passed = failed = ignored = 0
  next
}
/^test [^ ]+ \.\.\. (ok|FAILED|ignored)(,| |$)/ {
  if (!running) bad = 1
  result = $4; sub(/,$/, "", result)
  if (result == "ok") passed++
  else if (result == "FAILED") failed++
  else ignored++
  print $2, result
  next
}
/^test result: (ok|FAILED)\. [0-9]+ passed; [0-9]+ failed; [0-9]+ ignored;/ {
  if (!running || passed != $4 || failed != $6 || ignored != $8 ||
      passed + failed + ignored != planned) bad = 1
  ran += passed + failed; failures += failed; running = 0
}
END {
  if (bad || running || !ran || !(status == 0 && !failures || status == 101 && failures)) {
    print "incomplete or inconsistent compliance results: " FILENAME > "/dev/stderr"
    exit 1
  }
}
