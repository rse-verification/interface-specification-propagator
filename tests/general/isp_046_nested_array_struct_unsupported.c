/* run.config
EXIT: 1
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Nested arrays inside structs are reported as unsupported."
*/

enum RecordSlot {
  RECORD_LOW = 0,
  RECORD_HIGH = 1
};

struct Leaf {
  int value;
};

struct Record {
  struct Leaf items[2];
};

struct Record records[2];

struct Record helper_read_record(enum RecordSlot slot)
{
  return records[slot];
}

/*@ behavior interface_spec:
    assumes \true;
    assigns \nothing;
*/
void main(void)
{
  struct Record selected = helper_read_record(RECORD_HIGH);
  (void) selected.items[RECORD_LOW].value;
}
