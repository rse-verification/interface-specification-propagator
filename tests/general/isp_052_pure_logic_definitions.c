/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Pure definitional ACSL logic functions and predicates are copied without ISP-W001."
*/

/*@ logic integer increment(integer value) = value + 1; */

/*@ predicate is_positive(integer value) = value > 0; */

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
