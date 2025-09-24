from dataclasses import dataclass

@dataclass
class Geometry:
    road_x: int              # vertical road x-position
    train_w: int             # train length (nose->tail) in px
    approach_margin: int = 0 # kept for compatibility (unused here)


class LevelCrossingController:
    """
    Multi-track, sensor-driven barrier policy (immediate on nose contact).

    Track k has sensors A_k < B_k on the x-axis.

      Direction +1 (left→right):
        • CLOSE the instant NOSE >= A_k
        • OPEN  only when TAIL  >= B_k

      Direction -1 (right→left):
        • CLOSE the instant NOSE <= B_k
        • OPEN  only when TAIL  <= A_k

    Barrier command = DOWN if ANY track demands it.
    Reopen only when ALL tracks are clear (and fail-safe latch not active).

    `hazard_mode` simulates actuator fail-open: command state still changes,
    but the physical arm in the sim will ignore the down command.
    """

    def __init__(self,
                 geom: Geometry,
                 sensor_a_x_track1: int, sensor_b_x_track1: int,
                 sensor_a_x_track2: int, sensor_b_x_track2: int):
        self.geom = geom

        a1, b1 = sorted((sensor_a_x_track1, sensor_b_x_track1))
        a2, b2 = sorted((sensor_a_x_track2, sensor_b_x_track2))
        self.sensors = {0: (a1, b1), 1: (a2, b2)}

        # Modes / outputs
        self.barrier_down = False
        self.hazard_mode = False
        self.fail_safe_active = False
        self.fail_safe_triggered = False

        # Per-track runtime state
        self.tracks_in_section = {0: False, 1: False}
        self.track_demands_down = {0: False, 1: False}
        self.last_nose_x = {0: -10**9, 1: +10**9}  # note: sign helps wrap detection per direction

    # ---- legacy helper used by the sim for collision ----
    def train_in_crossing_zone(self, nose_x: int) -> bool:
        return nose_x <= self.geom.road_x <= nose_x + self.geom.train_w

    # ---- toggles ----
    def set_fail_safe(self, active: bool):
        if active and not self.fail_safe_active:
            self.fail_safe_triggered = True
        self.fail_safe_active = active

    def clear_state_for_loop_reset(self, track_id: int):
        self.tracks_in_section[track_id] = False
        self.track_demands_down[track_id] = False
        # Reset last nose far away so we won't miss the next approach
        self.last_nose_x[track_id] = -10**9 if track_id == 0 else +10**9

    # ---- core per-train update (call every frame per active train) ----
    def process_train_position_multi(self, track_id: int, nose_x: int, direction: int):
        """
        direction: +1 for left→right, -1 for right→left.
        nose_x is the x position of the train's front.
        """
        assert track_id in (0, 1)
        assert direction in (+1, -1)

        a_x, b_x = self.sensors[track_id]
        tail_x = nose_x + self.geom.train_w if direction == +1 else nose_x - self.geom.train_w

        # Detect wrap-around per direction so state resets correctly
        if direction == +1:
            if nose_x < self.last_nose_x[track_id] - self.geom.train_w:
                self.clear_state_for_loop_reset(track_id)
        else:  # direction == -1
            if nose_x > self.last_nose_x[track_id] + self.geom.train_w:
                self.clear_state_for_loop_reset(track_id)

        # -------- Immediate CLOSE on nose touching the first sensor --------
        if direction == +1:
            if nose_x >= a_x:  # nose contact with A
                self.tracks_in_section[track_id] = True
                self.track_demands_down[track_id] = True
        else:  # -1
            if nose_x <= b_x:  # nose contact with B
                self.tracks_in_section[track_id] = True
                self.track_demands_down[track_id] = True

        # -------- OPEN only after tail clears the far sensor --------
        if direction == +1:
            if tail_x >= b_x:  # tail cleared B
                self.tracks_in_section[track_id] = False
                self.track_demands_down[track_id] = False
        else:
            if tail_x <= a_x:  # tail cleared A
                self.tracks_in_section[track_id] = False
                self.track_demands_down[track_id] = False

        self.last_nose_x[track_id] = nose_x

    # ---- compute the final command once per frame ----
    def finalize_barrier_command(self):
        # Fail-safe keeps it down until all tracks are clear
        if self.fail_safe_active and not self.hazard_mode:
            self.barrier_down = True
            if not any(self.tracks_in_section.values()):
                self.fail_safe_active = False
            return

        demand = any(self.track_demands_down.values())

        # Even if hazard_mode is ON (physical arm won't move), we still update the command state.
        self.barrier_down = demand

    # ---- legacy single-track shim (not used but kept) ----
    def process_train_position(self, nose_x: int):
        self.process_train_position_multi(0, nose_x, +1)
        self.finalize_barrier_command()
