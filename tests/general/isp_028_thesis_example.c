/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Example for the thesis report."
*/

int WHEEL_SPEED;
int STATE;

typedef enum { STAND_STILL = 0, MOVING = 1 } VEHICLE_STATE;

void update_state() {
  if (WHEEL_SPEED > 0)
    STATE = MOVING;
  else
    STATE = STAND_STILL;
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&WHEEL_SPEED);
    requires \valid_read(&STATE);
    requires \valid(&STATE);
    requires WHEEL_SPEED ∈ (0..400);
    ensures STATE ∈ {0, 1};
    assigns STATE;
    */
void main() {
  update_state();
}
