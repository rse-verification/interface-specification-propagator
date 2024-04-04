/* run.config
OPT: -autoload-plugins -isp -isp-print
COMMENT: "Testing interface specifications detection."
*/

int X;
int Y;

int triple(int x) {
  return x * 3;
}

void set_y(int t) {
  Y = t;
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires \valid_read(&Y);
    requires \valid(&Y);
    requires X >= -5;
    requires X <= 10;
    ensures Y \in (-15..30);
    assigns Y;
    */
void main() {
  int t = triple(X);
  set_y(t);
}
