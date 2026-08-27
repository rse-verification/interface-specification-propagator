/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Soundness-relevant global ACSL annotations retain ISP-W001."
*/

int state;
volatile int sensor;

/*@ logic integer unspecified(integer value); */

/*@
  inductive nonnegative(integer value) {
    case nonnegative_zero: nonnegative(0);
    case nonnegative_step:
      \forall integer n; nonnegative(n) ==> nonnegative(n + 1);
  }
*/

/*@ global invariant state_is_nonnegative: state >= 0; */

/*@ lemma zero_is_zero: 0 == 0; */

/*@
  axiomatic TrustedFacts {
    axiom one_is_positive: 1 > 0;
  }
*/

/*@ volatile sensor; */

/*@ assigns \nothing; */
void main(void)
{
}
