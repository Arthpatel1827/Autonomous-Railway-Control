import pygame
import sys
import random
from dataclasses import dataclass
from typing import List, Optional, Tuple, Dict

from .constants import *
from . import view  # <<< import the module, not font variables
from .controller import LevelCrossingController, Geometry

# ===================== Controller & geometry ==================
geom = Geometry(road_x=ROAD_X, train_w=TRAIN_W)
ctl  = LevelCrossingController(geom, SENSOR_A_X, SENSOR_B_X, SENSOR_A_X, SENSOR_B_X)

# ===================== Simulation state =======================
@dataclass
class Car:
    x: int               # lane x (fixed)
    y: float             # top (front) y
    direction: int       # -1 = up (northbound), +1 = down (southbound)
    speed_pps: float = CAR_SPEED_PPS

cars: List[Car] = []
time_to_next_car = random.uniform(CAR_GAP_MIN, CAR_GAP_MAX)

@dataclass
class ActiveTrain:
    nose_x: float
    track_id: int      # 0 = top (L→R), 1 = bottom (R→L)
    direction: int     # +1 or -1

train: Optional[ActiveTrain] = None
time_to_next_train: float = random.uniform(TRAIN_GAP_MIN, TRAIN_GAP_MAX)

# Gate angles — INDEPENDENT per named barrier:
#   A = north EXIT  (north line, left post)
#   B = north ENTRY (north line, right post)
#   C = south ENTRY (south line, left post)
#   D = south EXIT  (south line, right post)
bar_ang: Dict[str, float] = {
    "A": BARRIER_UP_ANG,
    "B": BARRIER_UP_ANG,
    "C": BARRIER_UP_ANG,
    "D": BARRIER_UP_ANG,
}

flash_phase = 0.0

# ===================== Crossing occupancy =========
ZONE_TOP = BARRIER_Y_NORTH
ZONE_BOT = BARRIER_Y_SOUTH

def car_overlaps_crossing(c: Car) -> bool:
    top, bot = c.y, c.y + CAR_H
    return not (bot < ZONE_TOP or top > ZONE_BOT)

def northbound_in_zone() -> bool:
    return any(c.direction == -1 and car_overlaps_crossing(c) for c in cars)

def southbound_in_zone() -> bool:
    return any(c.direction == +1 and car_overlaps_crossing(c) for c in cars)

# ===================== Train helpers ==========================
def train_crossing_road(nose_x: float, dir_: int) -> bool:
    if dir_ == +1:
        return nose_x <= ROAD_X <= nose_x + TRAIN_W
    else:
        tail_x = nose_x - TRAIN_W
        return tail_x <= ROAD_X <= nose_x

def check_collision(active: Optional[ActiveTrain]) -> bool:
    if active is None:
        return False
    if not train_crossing_road(active.nose_x, active.direction):
        return False
    return any(car_overlaps_crossing(c) for c in cars)

def maybe_spawn_train() -> Optional[ActiveTrain]:
    track_id, direction = random.choice([(0, +1), (1, -1)])
    nose_x = -TRAIN_W if direction == +1 else WIDTH + TRAIN_W
    ctl.clear_state_for_loop_reset(track_id)
    return ActiveTrain(nose_x=nose_x, track_id=track_id, direction=direction)

# ===================== Car logic ==============================
def car_should_stop(curr_y: float, next_y: float, direction: int,
                    entry_down_north: bool, entry_down_south: bool) -> bool:
    """
    Stop ONLY at the entry barrier for the car's direction.
      - UP cars (dir=-1) stop at SOUTH entry (C).
      - DOWN cars (dir=+1) stop at NORTH entry (B).
    """
    if direction == -1:  # up → C (south entry)
        if not entry_down_south: return False
        return (curr_y > STOP_LINE_UP + STOP_EPS) and (next_y <= STOP_LINE_UP + STOP_EPS)
    else:                 # down → B (north entry)
        if not entry_down_north: return False
        return (curr_y < STOP_LINE_DOWN - STOP_EPS) and (next_y >= STOP_LINE_DOWN - STOP_EPS)

def spawn_car():
    global time_to_next_car
    if len(cars) >= MAX_CARS:
        time_to_next_car = random.uniform(CAR_GAP_MIN, CAR_GAP_MAX)
        return
    direction = random.choice([-1, +1])
    if direction == -1:
        lane_x = random.choice(UP_LANES_X)
        start_y = HEIGHT - 90 + random.uniform(-6, 6)
    else:
        lane_x = random.choice(DOWN_LANES_X)
        start_y = -CAR_H - 20 + random.uniform(-6, 6)
    cars.append(Car(x=lane_x, y=start_y, direction=direction, speed_pps=CAR_SPEED_PPS))
    time_to_next_car = random.uniform(CAR_GAP_MIN, CAR_GAP_MAX)

def maintain_headway_per_lane():
    groups: Dict[Tuple[int, int], List[Car]] = {}
    for c in cars:
        key = (c.direction, c.x)
        groups.setdefault(key, []).append(c)
    for (direction, lane_x), glist in groups.items():
        if direction == -1:  # up
            glist.sort(key=lambda c: c.y)
        else:                # down
            glist.sort(key=lambda c: -c.y)
        for i in range(1, len(glist)):
            ahead = glist[i-1]; car = glist[i]
            if direction == -1:
                car.y = max(car.y, ahead.y + CAR_H + MIN_HEADWAY_PX)
            else:
                car.y = min(car.y, ahead.y - CAR_H - MIN_HEADWAY_PX)

# ===================== Main loop ==============================
def run():
    global train, time_to_next_train, time_to_next_car, flash_phase, bar_ang

    pygame.init()
    screen = pygame.display.set_mode((WIDTH, HEIGHT))
    pygame.display.set_caption("Level Crossing — Barriers A/B/C/D")
    clock = pygame.time.Clock()
    view.init_fonts()   # <<< initialize fonts inside the module

    while True:
        dt = clock.tick(60) / 1000.0

        # Inputs
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit(); sys.exit()
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_h: ctl.hazard_mode = not ctl.hazard_mode
                if event.key == pygame.K_f: ctl.set_fail_safe(not ctl.fail_safe_active)
                if event.key == pygame.K_9:
                    for c in cars: c.speed_pps = max(15.0, c.speed_pps - 5.0)
                if event.key == pygame.K_0:
                    for c in cars: c.speed_pps = min(300.0, c.speed_pps + 5.0)

        # Background & sensors
        view.draw_scene_background(screen)
        view.draw_sensors(screen)

        # --- Train scheduling / movement ---
        active_info = "none"
        if train is None:
            time_to_next_train -= dt
            if time_to_next_train <= 0.0:
                train = maybe_spawn_train()
                active_info = f"spawn track {train.track_id} dir {train.direction:+d}"
            else:
                active_info = f"waiting ({time_to_next_train:.1f}s)"
        else:
            train.nose_x += train.direction * TRAIN_SPEED_PPS * dt
            active_info = f"track {train.track_id} dir {train.direction:+d}"
            ctl.process_train_position_multi(train.track_id, int(train.nose_x), train.direction)
            off_right = (train.direction == +1 and train.nose_x - TRAIN_W > WIDTH + 10)
            off_left  = (train.direction == -1 and train.nose_x + TRAIN_W < -10)
            if off_right or off_left:
                ctl.clear_state_for_loop_reset(train.track_id)
                train = None
                time_to_next_train = random.uniform(TRAIN_GAP_MIN, TRAIN_GAP_MAX)

        # Controller barrier command due to train sensors
        ctl.finalize_barrier_command()
        want_down = ctl.barrier_down and not ctl.hazard_mode   # ONLY trains trigger closure

        # -------- Barrier targets (A/B/C/D) ----------
        nb_in = northbound_in_zone()
        sb_in = southbound_in_zone()

        if not want_down:
            target_down = {"A": False, "B": False, "C": False, "D": False}
        else:
            target_down = {
                "A": not nb_in,   # A down unless northbound cars are inside
                "B": True,        # B always down with train (north entry closed)
                "C": True,        # C always down with train (south entry closed)
                "D": not sb_in,   # D down unless southbound cars are inside
            }

        # ---- Animate each named barrier toward its target ----
        for key in ("A", "B", "C", "D"):
            targ_ang = BARRIER_DOWN_ANG if target_down[key] else BARRIER_UP_ANG
            if bar_ang[key] < targ_ang:
                bar_ang[key] = min(targ_ang, bar_ang[key] + BARRIER_SWING_DPS * dt)
            elif bar_ang[key] > targ_ang:
                bar_ang[key] = max(targ_ang, bar_ang[key] - BARRIER_SWING_DPS * dt)

        # Lights blink per barrier if that barrier is target-down
        flash_phase += dt * FLASH_HZ
        blink = int(flash_phase) % 2 == 0
        north_light_left  = blink and target_down["A"]  # A (north-left, exit)
        north_light_right = blink and target_down["B"]  # B (north-right, entry)
        south_light_left  = blink and target_down["C"]  # C (south-left, entry)
        south_light_right = blink and target_down["D"]  # D (south-right, exit)

        # --- Draw train BEFORE gates so arms overlay correctly ---
        if train is not None:
            y_center = TRACK_Y_TOP if train.track_id == 0 else TRACK_Y_BOT
            view.draw_train(screen, train.nose_x, y_center, train.direction, TRAIN_W, TRAIN_H)

        # Draw lines with independent left/right barriers:
        #   North line: left=A (north exit), right=B (north entry)
        view.draw_barrier_line(screen, BARRIER_Y_NORTH,
                               "A", bar_ang["A"], north_light_left,
                               "B", bar_ang["B"], north_light_right)
        #   South line: left=C (south entry), right=D (south exit)
        view.draw_barrier_line(screen, BARRIER_Y_SOUTH,
                               "C", bar_ang["C"], south_light_left,
                               "D", bar_ang["D"], south_light_right)

        # --- Cars: spawn & move ---
        time_to_next_car -= dt
        if time_to_next_car <= 0.0:
            spawn_car()

        for car in cars:
            curr_y = car.y
            next_y = car.y + car.direction * car.speed_pps * dt
            stop = car_should_stop(curr_y, next_y, car.direction,
                                   entry_down_north=target_down["B"],  # B = north entry
                                   entry_down_south=target_down["C"])  # C = south entry
            if stop:
                next_y = curr_y
            car.y = next_y

        maintain_headway_per_lane()
        cars[:] = [c for c in cars if (-CAR_H-60) <= c.y <= (HEIGHT+60)]

        # --- Collision & HUD ---
        collision = check_collision(train)
        for car in cars:
            rect = pygame.Rect(int(car.x - CAR_W//2), int(car.y), CAR_W, CAR_H)
            view.draw_car(screen, rect)

        if collision:
            banner = view.banner_surface(RED, "⚠️  COLLISION!  Unsafe state", view.font_normal)
        elif getattr(ctl, "fail_safe_triggered", False):
            banner = view.banner_surface(BLACK, "Fail-safe: Barriers forced down", view.font_normal)
            ctl.fail_safe_triggered = False
        else:
            banner = view.banner_surface(BLACK, "System operating safely", view.font_normal)
        screen.blit(banner, (WIDTH//2 - banner.get_width()//2, 14))

        view.hud_text(screen, view.font_small, active_info, target_down,
                      time_to_next_train, time_to_next_car,
                      len(cars), MIN_HEADWAY_PX, CAR_SPEED_PPS,
                      ctl.hazard_mode, ctl.fail_safe_active)
        pygame.display.flip()

# For direct run
if __name__ == "__main__":
    run()
