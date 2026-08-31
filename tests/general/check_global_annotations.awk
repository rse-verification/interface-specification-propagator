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
    if (warning_count != 0 || !saw_increment || !saw_predicate || \
        (expect_memory_read && !saw_memory_read)) {
      print "defined global logic annotations were not preserved cleanly"
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
    print "expected six ISP-W001 diagnostics for unsupported global annotations"
    exit 1
  }

  print "unknown global-annotation check mode"
  exit 1
}
