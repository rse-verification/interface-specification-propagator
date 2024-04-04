/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing Lval index that evaluates to an interval."
*/

int X;
int Y[10];

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires \valid_read(Y+(1..8));
    requires \valid(Y+(1..8));
    requires Y[0..8] == 0;
    requires X >= 1 && X <= 8;
    ensures Y[1] >= 0 && Y[1] <= 8;
    ensures Y[2] >= 0 && Y[2] <= 8;
    ensures Y[3] >= 0 && Y[3] <= 8;
    ensures Y[4] >= 0 && Y[4] <= 8;
    ensures Y[5] >= 0 && Y[5] <= 8;
    ensures Y[6] >= 0 && Y[6] <= 8;
    ensures Y[7] >= 0 && Y[7] <= 8;
    ensures Y[8] >= 0 && Y[8] <= 8;
    assigns Y[1..8];
    */
void main() {
    Y[X] = X;
}
