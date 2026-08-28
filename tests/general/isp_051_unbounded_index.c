/* run.config
EXIT: 1
DEPS: check_index_expansion_boundary.awk
FILTER: awk -v expected=unbounded -f @PTEST_DIR@/check_index_expansion_boundary.awk
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "An index Eva cannot bound fails closed."
*/

int X;
int Y[2];

/*@ behavior interface_spec:
    assumes \true;
    assigns Y[0..1];
*/
int main(void)
{
  Y[X] = 1;
  return 0;
}
