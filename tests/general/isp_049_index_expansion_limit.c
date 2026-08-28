/* run.config
DEPS: check_index_expansion_boundary.awk
FILTER: awk -v expected=bounded -f @PTEST_DIR@/check_index_expansion_boundary.awk
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Exactly 1024 Eva-resolved indices remain supported."
*/

int X;
int Y[1024];

/*@ behavior interface_spec:
    assumes \true;
    requires 0 <= X <= 1023;
    requires \valid(Y + (0..1023));
    assigns Y[0..1023];
*/
int main(void)
{
  Y[X] = 1;
  return 0;
}
