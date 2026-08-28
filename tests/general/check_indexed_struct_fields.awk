{
  saw_input = 1
}

/^[[:space:]]*requires / {
  saw_contract_clause = 1
  if ($0 ~ /records\[1\]\.level/) requires_level = 1
  if ($0 ~ /records\[1\]\.status/) requires_status = 1
}

/^[[:space:]]*ensures / {
  saw_contract_clause = 1
  if ($0 ~ /records\[1\]\.level/) ensures_level = 1
  if ($0 ~ /records\[1\]\.status/) ensures_status = 1
}

/^[[:space:]]*assigns / {
  saw_contract_clause = 1
  in_assigns = 1
}

in_assigns {
  if ($0 ~ /records\[1\]\.level/) assigns_level = 1
  if ($0 ~ /records\[1\]\.status/) assigns_status = 1
  if ($0 ~ /;/) in_assigns = 0
}

END {
  if (!saw_input)
    exit 0

  if (!saw_contract_clause) {
    print "missing generated contract clauses"
    exit 1
  }

  if (requires_level && requires_status)
    print "requires retain records[1].level and records[1].status"
  else
    missing = 1

  if (ensures_level && ensures_status)
    print "ensures retain records[1].level and records[1].status"
  else
    missing = 1

  if (assigns_level && assigns_status)
    print "assigns retain records[1].level and records[1].status"
  else
    missing = 1

  exit missing
}
