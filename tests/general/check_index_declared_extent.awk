{
  saw_input = 1
}

/ISP-E012/ {
  saw_e012 = 1
}

END {
  if (!saw_input)
    exit 0

  if (saw_e012) {
    print "out-of-bounds expanded index is rejected with ISP-E012"
    exit 0
  }
  print "missing ISP-E012 for out-of-bounds expanded index"
  exit 1
}
