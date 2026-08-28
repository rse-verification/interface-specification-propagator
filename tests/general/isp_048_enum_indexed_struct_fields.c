/* run.config
DEPS: check_indexed_struct_fields.awk
FILTER: awk -f @PTEST_DIR@/check_indexed_struct_fields.awk
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Multiple fields at the same Eva-resolved enum index retain distinct contracts."
*/

enum RecordSlot {
  RECORD_LOW = 0,
  RECORD_HIGH = 1
};

struct SlotRecord {
  int level;
  int status;
};

struct SlotRecord records[2] = {
  {3, 0},
  {8, 1}
};

int update_record(enum RecordSlot slot)
{
  int previous = records[slot].level + records[slot].status;
  records[slot].level = 11;
  records[slot].status = 22;
  return previous;
}

/*@ behavior interface_spec:
    assumes \true;
    assigns \nothing;
*/
int main(void)
{
  (void) update_record(RECORD_HIGH);
  return 0;
}
