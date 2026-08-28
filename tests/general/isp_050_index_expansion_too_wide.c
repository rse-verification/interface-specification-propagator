/* run.config
EXIT: 1
DEPS: check_index_expansion_boundary.awk
FILTER: awk -v expected=oversized -f @PTEST_DIR@/check_index_expansion_boundary.awk
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "More than 1024 Eva-resolved indices fail closed."
*/

int X;
int Y[1025];

/*@ behavior interface_spec:
    assumes \true;
    requires 0 <= X <= 1024;
    requires \valid(Y + (0..1024));
    assigns Y[0..1024];
*/
int main(void)
{
  Y[X] = 1;
  return 0;
}
