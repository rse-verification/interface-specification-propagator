{
  saw_input = 1
}

/ISP-E011/ {
  saw_e011 = 1
}

/requires \\valid\(&Y\[0\]\);/ {
  saw_lower_endpoint = 1
}

/requires \\valid\(\(int \*\)Y\);/ {
  saw_lower_endpoint = 1
}

/requires \\valid\(&Y\[1023\]\);/ {
  saw_upper_endpoint = 1
}

END {
  if (!saw_input)
    exit 0

  if (expected == "bounded") {
    if (!saw_e011 && saw_lower_endpoint && saw_upper_endpoint) {
      print "1024-value expansion retains both endpoints"
      exit 0
    }
    print "1024-value expansion was rejected or lost an endpoint"
    exit 1
  }

  if (expected == "oversized") {
    if (saw_e011) {
      print "1025-value expansion is rejected with ISP-E011"
      exit 0
    }
    print "missing ISP-E011 for 1025-value expansion"
    exit 1
  }

  if (expected == "unbounded") {
    if (saw_e011) {
      print "unbounded index is rejected with ISP-E011"
      exit 0
    }
    print "missing ISP-E011 for unbounded index"
    exit 1
  }

  print "unknown boundary-check mode"
  exit 1
}
