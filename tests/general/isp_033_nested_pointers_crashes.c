/* run.config
EXIT: 125
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing deep nested pointers. Crashes right now."
*/

int X;

void extra_increment(int** x) {
  **x += 1;
}

void increment(int* x) {
  *x += 1;
  extra_increment(&x);
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires X == 1;
    ensures \result == 3;
    assigns \nothing;
    */
int main() {
  int temp = X;
  increment(&temp);
  return temp;
}
