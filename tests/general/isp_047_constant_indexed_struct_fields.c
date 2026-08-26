/* run.config
DEPS: check_indexed_struct_fields.awk
FILTER: awk -f @PTEST_DIR@/check_indexed_struct_fields.awk
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Multiple fields at the same constant array index retain distinct contracts."
*/

struct SlotRecord {
  int level;
  int status;
};

struct SlotRecord records[2] = {
  {3, 0},
  {8, 1}
};

int update_record(void)
{
  int previous = records[1].level + records[1].status;
  records[1].level = 11;
  records[1].status = 22;
  return previous;
}

/*@ behavior interface_spec:
    assumes \true;
    assigns \nothing;
*/
int main(void)
{
  (void) update_record();
  return 0;
}
