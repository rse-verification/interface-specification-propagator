/* run.config
DEPS: check_global_annotations.awk
FILTER: awk -v expected=defined -v expect_memory_read=1 -f @PTEST_DIR@/check_global_annotations.awk
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Defined ACSL logic functions and predicates are copied without ISP-W001."
*/

/*@ logic integer increment(integer value) = value + 1; */

/*@ predicate is_positive(integer value) = value > 0; */

/*@ logic integer read_value{L}(int *p) = *p; */

int helper(int value)
{
  return value + 1;
}

/*@
  requires -100 <= value <= 100;
  ensures \result == increment(value);
  ensures is_positive(value) ==> \result > 1;
*/
int main(int value)
{
  return helper(value);
}
