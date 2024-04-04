/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing Lval index that evaluates to a small set of values."
*/

int X;
int Y[10];

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires \valid_read(Y+(1..7));
    requires \valid(Y+(1..7));
    requires Y[0..9] == 0;
    requires X >= 1 && X <= 7;
    ensures Y[1] ∈ {0, 1, 2, 3, 4, 5, 6, 7};
    ensures Y[2] ∈ {0, 1, 2, 3, 4, 5, 6, 7};
    ensures Y[3] ∈ {0, 1, 2, 3, 4, 5, 6, 7};
    ensures Y[4] ∈ {0, 1, 2, 3, 4, 5, 6, 7};
    ensures Y[5] ∈ {0, 1, 2, 3, 4, 5, 6, 7};
    ensures Y[6] ∈ {0, 1, 2, 3, 4, 5, 6, 7};
    ensures Y[7] ∈ {0, 1, 2, 3, 4, 5, 6, 7};
    assigns Y[1..7];
    */
void main() {
    Y[X] = X;
}
