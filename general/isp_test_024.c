/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Function arguments with unused arguments, non-pointer."
*/

int X;

int increment(int x, int y) {
  x = 2;
  x += 1;
  return x;
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires X == 1;
    ensures \result == 3;
    assigns \nothing;
    */
int main() {
  int temp = increment(X, 0);
  return temp;
}
