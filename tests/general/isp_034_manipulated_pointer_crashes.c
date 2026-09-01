/* run.config
EXIT: 125
DEPS: check_unsupported_pointer_crash.awk
FILTER: awk -f @PTEST_DIR@/check_unsupported_pointer_crash.awk
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Computed pointer lvalues report ISP-W003 and the known ISP-E005 failure."
*/

int X;

void increment(int* x) {
  *((x+1)-1) += 1;
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires X == 1;
    ensures \result == 2;
    assigns \nothing;
    */
int main() {
  int temp = X;
  increment(&temp);
  return temp;
}
