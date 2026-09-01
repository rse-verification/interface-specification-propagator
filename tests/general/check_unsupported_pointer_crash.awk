{
  saw_input = 1
}

/\[ISP-W003\]/ {
  saw_w003 = 1
}

/\[ISP-E005\]/ {
  saw_e005 = 1
}

END {
  if (!saw_input)
    exit 0

  if (saw_w003 && saw_e005) {
    print "unsupported pointer lvalue reports ISP-W003 and ISP-E005"
    exit 0
  }

  print "expected ISP-W003 followed by ISP-E005 for an unsupported pointer lvalue"
  exit 1
}
