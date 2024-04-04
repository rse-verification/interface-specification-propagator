/* run.config
OPT: -autoload-plugins -isp -isp-print
COMMENT: "Testing floating points intervals."
*/

double X;
double Y;

double triple(double x) {
  return x * 3.0;
}

void set_y(double t) {
  Y = t;
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires \valid_read(&Y);
    requires \valid(&Y);
    requires X >= 0;
    requires X <= 10;
    ensures Y >= 0 && Y <= 30;
    assigns Y;
    */
void main() {
  double t = triple(X);
  set_y(t);
}
