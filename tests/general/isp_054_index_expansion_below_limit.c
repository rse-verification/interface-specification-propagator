/* run.config
DEPS: check_index_expansion_boundary.awk
FILTER: awk -v expected=bounded -v upper=1022 -f @PTEST_DIR@/check_index_expansion_boundary.awk
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "A bounded range below the expansion limit retains both endpoints."
*/

int X;
int Y[1023];

/*@ behavior interface_spec:
    assumes \true;
    requires 0 <= X <= 1022;
    requires \valid(Y + (0..1022));
    assigns Y[0..1022];
*/
int main(void)
{
  Y[X] = 1;
  return 0;
}
