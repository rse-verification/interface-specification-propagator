{
  saw_input = 1
}

/\[ISP-W001\]/ {
  warning_count++
}

/logic .*increment/ {
  saw_increment = 1
}

/predicate is_positive/ {
  saw_predicate = 1
}

/logic .*read_value/ {
  saw_memory_read = 1
}

END {
  if (!saw_input)
    exit 0

  if (expected == "defined") {
    if (warning_count != 0) {
      print "unexpected ISP-W001 for a defined logic annotation"
      exit 1
    }
    if (!saw_increment) {
      print "copied output is missing logic function increment"
      exit 1
    }
    if (!saw_predicate) {
      print "copied output is missing predicate is_positive"
      exit 1
    }
    if (expect_memory_read && !saw_memory_read) {
      print "copied output is missing logic function read_value"
      exit 1
    }
    if (expect_memory_read)
      print "defined global logic annotations, including a memory read, are preserved without ISP-W001"
    else
      print "defined global logic annotations are preserved without ISP-W001"
    exit 0
  }

  if (expected == "unsupported") {
    if (warning_count == 6) {
      print "six unsupported global annotation forms report ISP-W001"
      exit 0
    }
    print "expected 6 ISP-W001 diagnostics; found " warning_count
    exit 1
  }

  print "unknown global-annotation check mode: " expected
  exit 1
}
