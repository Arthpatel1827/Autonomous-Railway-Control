import pygame
import sys
import random
from dataclasses import dataclass
from typing import List, Optional, Tuple, Dict
from math import cos, sin, radians
from simulation.controller import LevelCrossingController, Geometry

# ===================== Layout & constants =====================
WIDTH, HEIGHT = 1800, 900

# Two horizontal tracks (top & bottom)
TRACK_Y_TOP = 262
TRACK_Y_BOT = 338
TRACKS = (TRACK_Y_TOP, TRACK_Y_BOT)

# Road centered horizontally
ROAD_X = WIDTH // 2
ROAD_HALF = 120              # half width of paved road (6 lanes total)
POST_CLEAR = 12              # gate posts sit this far OUTSIDE the road edge

# --- Barriers: posts OUTSIDE the road ---
BARRIER_OFFSET = 70          # distance from nearest track center to the gate line
BARRIER_Y_NORTH = TRACK_Y_TOP - BARRIER_OFFSET
BARRIER_Y_SOUTH = TRACK_Y_BOT + BARRIER_OFFSET

TRAIN_W, TRAIN_H = 240, 56
CAR_W, CAR_H     = 46, 70

# Speeds (pixels/second)
TRAIN_SPEED_PPS = 170.0
CAR_SPEED_PPS   = 140.0

# Train arrival randomness (seconds)
TRAIN_GAP_MIN = 2.5
TRAIN_GAP_MAX = 6.0

# ---- Cars: 6 lanes & random spawn gaps ----
NUM_LANES = 6
LANE_W = (2 * ROAD_HALF) / NUM_LANES
LANE_CENTERS = [ROAD_X - ROAD_HALF + (i + 0.5) * LANE_W for i in range(NUM_LANES)]
UP_LANES_X   = LANE_CENTERS[0:3]  # left 3 lanes go UP (northbound, dir=-1)
DOWN_LANES_X = LANE_CENTERS[3:6]  # right 3 lanes go DOWN (southbound, dir=+1)

CAR_GAP_MIN = 0.5
CAR_GAP_MAX = 2.0
MAX_CARS    = 60
MIN_HEADWAY_PX = 60

# Barrier (visual)
BARRIER_LEN        = ROAD_HALF - 8     # arm reaches into road from the post
BARRIER_DOWN_ANG   = 0
BARRIER_UP_ANG     = 80
BARRIER_SWING_DPS  = 180

# Flashing lights
FLASH_HZ = 1.2

# Sensors (A left, B right)
SENSOR_OFFSET = 850
SENSOR_A_X    = ROAD_X - SENSOR_OFFSET
SENSOR_B_X    = ROAD_X + SENSOR_OFFSET

# Stop lines:
#  • UP cars stop just BEFORE the SOUTH entry gate line (SEB).
#  • DOWN cars stop just BEFORE the NORTH entry gate line (NLB).
STOP_LINE_UP   = BARRIER_Y_SOUTH + 10                       # entry from south
STOP_LINE_DOWN = BARRIER_Y_NORTH - CAR_H - 10               # entry from north
STOP_EPS = 0.5

# ===================== Pygame setup ===========================
pygame.init()
screen = pygame.display.set_mode((WIDTH, HEIGHT))
pygame.display.set_caption("Level Crossing — Correct Exit-Only Opening, 4 Named Barriers")
clock = pygame.time.Clock()
font_small  = pygame.font.SysFont("Arial", 18)
font_normal = pygame.font.SysFont("Arial", 28, bold=True)
font_label  = pygame.font.SysFont("Arial", 14, bold=True)

# Colors
SKY=(225,240,255); GROUND=(210,225,210); ROAD_ASP=(210,210,210)
RAIL=(35,35,35); SLEEPER=(120,85,60)
WHITE=(255,255,255); BLACK=(0,0,0); RED=(205,40,40); RED_DARK=(160,20,20)
GREEN=(40,180,70); GREEN_D=(35,140,55); BLUE=(40,80,210)
YELLOW=(250,220,70); ORANGE=(255,160,60)

# ===================== Controller & geometry ==================
geom = Geometry(road_x=ROAD_X, train_w=TRAIN_W)
# Controller must support multi-track sensor API used below
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
# NEB (north exit), NLB (north entry), SEB (south entry), SLB (south exit)
bar_ang = {
    "NEB": BARRIER_UP_ANG,
    "NLB": BARRIER_UP_ANG,
    "SEB": BARRIER_UP_ANG,
    "SLB": BARRIER_UP_ANG,
}
flash_phase = 0.0

# ===================== Drawing helpers ========================
def draw_round_rect(surf, rect, color, radius=8):
    pygame.draw.rect(surf, color, rect, border_radius=radius)

def draw_shadow_rect(surf, rect, blur_alpha=40):
    shadow = pygame.Surface((rect[2], rect[3]), pygame.SRCALPHA)
    shadow.fill((0, 0, 0, blur_alpha))
    surf.blit(shadow, (rect[0]+2, rect[1]+2))

def draw_lane_markings():
    dash = 22
    gap  = 16
    for i in range(1, NUM_LANES):
        x = ROAD_X - ROAD_HALF + i * LANE_W
        if i == 3:  # double-yellow divider between directions
            for y in range(0, HEIGHT, dash + gap):
                pygame.draw.line(screen, (240, 200, 0), (x-3, y), (x-3, min(y+dash, HEIGHT)), 3)
                pygame.draw.line(screen, (240, 200, 0), (x+3, y), (x+3, min(y+dash, HEIGHT)), 3)
        else:
            for y in range(0, HEIGHT, dash + gap):
                pygame.draw.line(screen, WHITE, (x, y), (x, min(y+dash, HEIGHT)), 2)

def draw_scene_background():
    screen.fill(SKY)
    pygame.draw.rect(screen, GROUND, (0, TRACK_Y_BOT + 120, WIDTH, HEIGHT - (TRACK_Y_BOT + 120)))

    # Road
    pygame.draw.rect(screen, ROAD_ASP, (ROAD_X - ROAD_HALF, 0, 2*ROAD_HALF, HEIGHT))
    pygame.draw.line(screen, BLACK, (ROAD_X-ROAD_HALF, 0), (ROAD_X-ROAD_HALF, HEIGHT), 3)
    pygame.draw.line(screen, BLACK, (ROAD_X+ROAD_HALF, 0), (ROAD_X+ROAD_HALF, HEIGHT), 3)
    draw_lane_markings()

    # Tracks
    for ty in TRACKS:
        for x in range(-40, WIDTH + 40, 40):
            pygame.draw.rect(screen, SLEEPER, (x, ty - 18, 26, 36))
        pygame.draw.line(screen, RAIL, (0, ty-14), (WIDTH, ty-14), 6)
        pygame.draw.line(screen, RAIL, (0, ty+14), (WIDTH, ty+14), 6)

def draw_sensors():
    for ty in TRACKS:
        pygame.draw.rect(screen, ORANGE, (SENSOR_A_X-3, ty-22, 6, 44), border_radius=2)
        pygame.draw.rect(screen, ORANGE, (SENSOR_B_X-3, ty-22, 6, 44), border_radius=2)
    la = font_small.render("A", True, BLACK); lb = font_small.render("B", True, BLACK)
    screen.blit(la, (SENSOR_A_X-6, TRACK_Y_TOP-36)); screen.blit(lb, (SENSOR_B_X-6, TRACK_Y_TOP-36))

def draw_train(nose_x: float, y_center: int, direction: int):
    if direction == +1:
        body_rect = pygame.Rect(int(nose_x), y_center - TRAIN_H//2, TRAIN_W, TRAIN_H)
        nose_px = body_rect.right
    else:
        body_rect = pygame.Rect(int(nose_x - TRAIN_W), y_center - TRAIN_H//2, TRAIN_W, TRAIN_H)
        nose_px = body_rect.left
    draw_shadow_rect(screen, body_rect)
    draw_round_rect(screen, body_rect, BLUE, radius=10)
    cab_w = 56
    if direction == +1:
        cab_rect = pygame.Rect(body_rect.right - cab_w, y_center - TRAIN_H//2 - 6, cab_w, TRAIN_H + 12)
    else:
        cab_rect = pygame.Rect(body_rect.left, y_center - TRAIN_H//2 - 6, cab_w, TRAIN_H + 12)
    draw_round_rect(screen, cab_rect, (25, 60, 180), radius=10)
    for i in range(3):
        wx = body_rect.left + 20 + i*60
        wy = y_center - TRAIN_H//2 + 8
        draw_round_rect(screen, (wx, wy, 36, 18), (180, 220, 255), radius=4)
    pygame.draw.circle(screen, YELLOW, (nose_px - (12 if direction==+1 else -12), y_center), 6)

def _draw_barrier_arm(hinge_x, hinge_y, angle_deg, extend_positive=True):
    ang = radians(angle_deg)
    arm_len, arm_h = BARRIER_LEN, 10
    if extend_positive:
        pts_local = [(0, -arm_h/2), (arm_len, -arm_h/2), (arm_len, arm_h/2), (0, arm_h/2)]
    else:
        pts_local = [(0, -arm_h/2), (-arm_len, -arm_h/2), (-arm_len, arm_h/2), (0, arm_h/2)]
    rot = []
    for px, py in pts_local:
        rx = hinge_x + px*cos(ang) - py*sin(ang)
        ry = hinge_y + px*sin(ang) + py*cos(ang)
        rot.append((rx, ry))
    pygame.draw.polygon(screen, RED, rot)
    # stripes
    for i in range(0, arm_len, 20):
        if extend_positive:
            sx0 = hinge_x + (i+4)*cos(ang);  sy0 = hinge_y + (i+4)*sin(ang)
            sx1 = hinge_x + (i+14)*cos(ang); sy1 = hinge_y + (i+14)*sin(ang)
        else:
            sx0 = hinge_x + (-(i+4))*cos(ang);  sy0 = hinge_y + (-(i+4))*sin(ang)
            sx1 = hinge_x + (-(i+14))*cos(ang); sy1 = hinge_y + (-(i+14))*sin(ang)
        pygame.draw.line(screen, WHITE, (sx0, sy0), (sx1, sy1), 3)

def draw_barrier_line(y_line: int,
                      left_label: str, left_angle: float, left_light_on: bool,
                      right_label: str, right_angle: float, right_light_on: bool):
    """Draw both posts on a line with INDEPENDENT angles/labels/lights."""
    left_post_x  = ROAD_X - ROAD_HALF - POST_CLEAR
    right_post_x = ROAD_X + ROAD_HALF + POST_CLEAR

    # Posts
    for px in (left_post_x, right_post_x):
        pygame.draw.rect(screen, BLACK, (px-6, y_line-50, 12, 100))
        pygame.draw.rect(screen, RED_DARK, (px-5, y_line-18, 10, 36))

    # Arms
    _draw_barrier_arm(left_post_x,  y_line, left_angle,  extend_positive=True)   # left extends +x
    _draw_barrier_arm(right_post_x, y_line, right_angle, extend_positive=False)  # right extends -x

    # Lights
    r = 9
    left_light  = (left_post_x + 14,  y_line - 20)
    right_light = (right_post_x - 14, y_line - 20)
    pygame.draw.circle(screen, RED_DARK, left_light,  r)
    pygame.draw.circle(screen, RED_DARK, right_light, r)
    if left_light_on:  pygame.draw.circle(screen, RED, left_light,  r)
    if right_light_on: pygame.draw.circle(screen, RED, right_light, r)

    # Labels
    lbl_left  = font_label.render(left_label,  True, BLACK)
    lbl_right = font_label.render(right_label, True, BLACK)
    screen.blit(lbl_left,  (left_post_x  - lbl_left.get_width()//2,  y_line - 70))
    screen.blit(lbl_right, (right_post_x - lbl_right.get_width()//2, y_line - 70))

def draw_car(car: Car):
    rect = pygame.Rect(int(car.x - CAR_W//2), int(car.y), CAR_W, CAR_H)
    draw_shadow_rect(screen, rect)
    draw_round_rect(screen, rect, GREEN, radius=8)
    roof = pygame.Rect(rect.x+6, rect.y+6,  CAR_W-12, 18)
    win  = pygame.Rect(rect.x+9, rect.y+12, CAR_W-18, 16)
    draw_round_rect(screen, roof, GREEN_D, radius=6)
    draw_round_rect(screen, win,  (190, 230, 255), radius=4)

def hud_text(active_info: str, states: Dict[str, bool]):
    sNEB = "DOWN" if states["NEB"] else "UP"
    sNLB = "DOWN" if states["NLB"] else "UP"
    sSEB = "DOWN" if states["SEB"] else "UP"
    sSLB = "DOWN" if states["SLB"] else "UP"
    lines = [
        f"Train: {active_info}   Next train in: {time_to_next_train:.1f}s   Next car in: {time_to_next_car:.1f}s",
        f"Barriers  NEB:{sNEB}  NLB:{sNLB}  SEB:{sSEB}  SLB:{sSLB}",
        f"Cars: {len(cars)}  Headway/ln: {MIN_HEADWAY_PX}px  Car speed: {CAR_SPEED_PPS:.0f}px/s   (H hazard: {'ON' if ctl.hazard_mode else 'OFF'}, F fail-safe: {'ON' if ctl.fail_safe_active else 'OFF'})",
    ]
    for i, txt in enumerate(lines):
        s = font_small.render(txt, True, BLACK)
        screen.blit(s, (10, HEIGHT - 70 + i*20))

# ===================== Car logic ==============================
def car_should_stop(curr_y: float, next_y: float, direction: int,
                    entry_down_north: bool, entry_down_south: bool) -> bool:
    """
    Stop ONLY at the entry barrier for the car's direction.
      - UP cars (dir=-1) stop at SOUTH entry (SEB).
      - DOWN cars (dir=+1) stop at NORTH entry (NLB).
    """
    if direction == -1:  # up → SEB
        if not entry_down_south: return False
        return (curr_y > STOP_LINE_UP + STOP_EPS) and (next_y <= STOP_LINE_UP + STOP_EPS)
    else:                 # down → NLB
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

# --------- Crossing occupancy ----------
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
    for c in cars:
        if car_overlaps_crossing(c):
            return True
    return False

# --- Train scheduling ---
def maybe_spawn_train() -> Optional[ActiveTrain]:
    track_id, direction = random.choice([(0, +1), (1, -1)])
    nose_x = -TRAIN_W if direction == +1 else WIDTH + TRAIN_W
    ctl.clear_state_for_loop_reset(track_id)
    return ActiveTrain(nose_x=nose_x, track_id=track_id, direction=direction)

# ===================== Main loop ==============================
def run():
    global train, time_to_next_train, time_to_next_car, flash_phase

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
        draw_scene_background()
        draw_sensors()

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

        # -------- Barrier target logic (entries & exits independent) ----------
        nb_in = northbound_in_zone()
        sb_in = southbound_in_zone()

        if not want_down:
            # No train ⇒ all barriers UP; cars flow freely
            target_down = {"SEB": False, "NLB": False, "NEB": False, "SLB": False}
        else:
            # Train active:
            #  - Entries must stay closed (no new cars enter from either side)
            #  - Open ONLY the matching exit if cars of that direction are inside
            target_down = {
                "SEB": True,              # south entry closed
                "NLB": True,              # north entry closed
                "NEB": not nb_in,         # north exit open only if northbound cars inside
                "SLB": not sb_in,         # south exit open only if southbound cars inside
            }

        # ---- Animate each named barrier toward its target ----
        for key in ("NEB", "NLB", "SEB", "SLB"):
            targ_ang = BARRIER_DOWN_ANG if target_down[key] else BARRIER_UP_ANG
            if bar_ang[key] < targ_ang:
                bar_ang[key] = min(targ_ang, bar_ang[key] + BARRIER_SWING_DPS * dt)
            elif bar_ang[key] > targ_ang:
                bar_ang[key] = max(targ_ang, bar_ang[key] - BARRIER_SWING_DPS * dt)

        # Lights blink per barrier if that barrier is target-down
        flash_phase += dt * FLASH_HZ
        blink = int(flash_phase) % 2 == 0
        north_light_left  = blink and target_down["NEB"]
        north_light_right = blink and target_down["NLB"]
        south_light_left  = blink and target_down["SEB"]
        south_light_right = blink and target_down["SLB"]

        # --- Draw train BEFORE gates so arms overlay correctly ---
        if train is not None:
            y_center = TRACK_Y_TOP if train.track_id == 0 else TRACK_Y_BOT
            draw_train(train.nose_x, y_center, train.direction)

        # Draw lines with independent left/right barriers:
        #   North line: left=NEB (north exit), right=NLB (north entry)
        draw_barrier_line(BARRIER_Y_NORTH,
                          "NEB", bar_ang["NEB"], north_light_left,
                          "NLB", bar_ang["NLB"], north_light_right)
        #   South line: left=SEB (south entry), right=SLB (south exit)
        draw_barrier_line(BARRIER_Y_SOUTH,
                          "SEB", bar_ang["SEB"], south_light_left,
                          "SLB", bar_ang["SLB"], south_light_right)

        # --- Cars: spawn & move ---
        time_to_next_car -= dt
        if time_to_next_car <= 0.0:
            spawn_car()

        # Cars stop only at their ENTRY barrier states:
        for car in cars:
            curr_y = car.y
            next_y = car.y + car.direction * car.speed_pps * dt
            stop = car_should_stop(curr_y, next_y, car.direction,
                                   entry_down_north=target_down["NLB"],   # NLB = north entry
                                   entry_down_south=target_down["SEB"])   # SEB = south entry
            if stop:
                next_y = curr_y
            car.y = next_y

        maintain_headway_per_lane()
        cars[:] = [c for c in cars if (-CAR_H-60) <= c.y <= (HEIGHT+60)]

        # --- Collision & HUD ---
        collision = check_collision(train)
        for car in cars: draw_car(car)

        if collision:
            banner = font_normal.render("⚠️  COLLISION!  Unsafe state", True, RED)
        elif getattr(ctl, "fail_safe_triggered", False):
            banner = font_normal.render("Fail-safe: Barriers forced down", True, BLACK); ctl.fail_safe_triggered = False
        else:
            banner = font_normal.render("System operating safely", True, BLACK)
        screen.blit(banner, (WIDTH//2 - banner.get_width()//2, 14))

        hud_text(active_info, target_down)
        pygame.display.flip()

# For direct run
if __name__ == "__main__":
    run()
