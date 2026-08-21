/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing enum-indexed array access followed by a struct field."
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

struct SlotRecord helper_read_record(enum RecordSlot slot)
{
  return records[slot];
}

/*@ behavior interface_spec:
    assumes \true;
    assigns \nothing;
*/
void main(void)
{
  struct SlotRecord selected = helper_read_record(RECORD_HIGH);
  (void) selected.level;
}
