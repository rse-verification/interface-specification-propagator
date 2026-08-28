/* run.config
DEPS: check_index_declared_extent.awk
FILTER: awk -f @PTEST_DIR@/check_index_declared_extent.awk
COMMENT: "An Eva-resolved array index interval crossing zero fails closed."
EXIT: 1
OPT: -no-check -autoload-plugins -isp -isp-print
*/

int X;
int Y[4];

/*@ behavior interface_spec:
    assumes \true;
    requires -1 <= X <= 2;
    assigns Y[0..3];
*/
int main(void)
{
  Y[X] = 1;
  return 0;
}
