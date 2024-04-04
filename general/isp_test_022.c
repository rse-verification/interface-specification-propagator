/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing pointers."
*/

int X;

void increment(int* x) {
  *x += 1;
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
