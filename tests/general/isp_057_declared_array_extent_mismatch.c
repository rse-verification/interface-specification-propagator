/* run.config
DEPS: check_index_declared_extent.awk
FILTER: awk -f @PTEST_DIR@/check_index_declared_extent.awk
COMMENT: "An Eva range wider than the declared array extent fails closed."
EXIT: 1
OPT: -no-check -autoload-plugins -isp -isp-print
*/

int X;
int Y[2];

/*@ behavior interface_spec:
    assumes \true;
    requires 0 <= X <= 2;
    requires \valid(Y + (0..1));
    assigns Y[0..1];
*/
int main(void)
{
  Y[X] = 1;
  return 0;
}
