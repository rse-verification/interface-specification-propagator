/* run.config
EXIT: 125
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing manipulated pointer. Crashes right now."
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
