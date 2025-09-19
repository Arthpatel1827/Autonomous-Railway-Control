from dataclasses import dataclass

@dataclass
class Geometry:
    road_x: int        # vertical road x-position
    train_w: int       # train length in px
    approach_margin: int  # how far before/after road the approach zone extends


class LevelCrossingController:
    """
    Deterministic, zone-based controller:
      - Barrier DOWN if train in APPROACH or CROSSING zone.
      - Barrier UP only when train is fully CLEAR of both zones.
      - Optional fail-safe latch that keeps barrier DOWN until clear.
      - 'hazard_mode' simulates barrier actuator failure (stays UP).
    """
    def __init__(self, geom: Geometry):
        self.geom = geom
        self.barrier_down = False

        # Fail-safe latch (e.g., sensor health issue): set True to force DOWN
        self.fail_safe_active = False
        self.fail_safe_triggered = False

        # Demo: simulate barrier failure (won't go down)
        self.hazard_mode = False

    # ---- Train zones (pure geometry) -------------------------------------

    def train_in_crossing_zone(self, train_x: int) -> bool:
        """Train body overlaps the vertical road line at road_x."""
        return (train_x <= self.geom.road_x <= train_x + self.geom.train_w)

    def train_in_approach_zone(self, train_x: int) -> bool:
        """
        Wider zone around the road to pre-close the barrier.
        Example: +- approach_margin beyond the road line, also considers train length.
        """
        start = self.geom.road_x - self.geom.approach_margin - self.geom.train_w
        end   = self.geom.road_x + self.geom.approach_margin
        return start <= train_x <= end

    def train_clear_of_all_zones(self, train_x: int) -> bool:
        return not self.train_in_crossing_zone(train_x) and not self.train_in_approach_zone(train_x)

    # ---- Public control update -------------------------------------------

    def set_fail_safe(self, active: bool):
        """Manually set/clear fail-safe (useful if you add a key later)."""
        if active and not self.fail_safe_active:
            self.fail_safe_triggered = True
        self.fail_safe_active = active

    def update(self, train_x: int):
        """
        Compute barrier command for this frame.
        Barrier DOWN if:
          - train in APPROACH zone OR CROSSING zone, OR
          - fail-safe active
        Otherwise UP.
        'hazard_mode' simulates a failed actuator that prevents lowering.
        """
        in_approach = self.train_in_approach_zone(train_x)
        in_crossing = self.train_in_crossing_zone(train_x)
        need_down = in_approach or in_crossing or self.fail_safe_active

        # Auto-release fail-safe once totally clear (no risk remains)
        if self.fail_safe_active and self.train_clear_of_all_zones(train_x):
            self.fail_safe_active = False

        # Command output (respecting hazard demo)
        if need_down and not self.hazard_mode:
            self.barrier_down = True
        else:
            self.barrier_down = False
