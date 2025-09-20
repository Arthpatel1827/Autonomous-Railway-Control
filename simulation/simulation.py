
import pygame
import sys
from dataclasses import dataclass
from typing import List
from math import cos, sin, radians
from simulation.controller import LevelCrossingController, Geometry

# ===================== Layout & constants =====================
WIDTH, HEIGHT     = 1000, 560
TRACK_Y           = 300                    # horizontal tracks center
ROAD_X            = 520                    # vertical road x (cars move along this)
BARRIER_Y         = TRACK_Y + 44           # barrier hinge y (on road edge)

TRAIN_W, TRAIN_H  = 240, 56
CAR_W, CAR_H      = 46, 70

# Speeds (pixels/second) — frame-rate independent
TRAIN_SPEED_PPS   = 170.0
CAR_SPEED_PPS     = 95.0

# Barrier timing (pre-close window)
T_CLOSE_SEC       = 1.2
SAFETY_BUFFER_PX  = 24

# Car flow
SPAWN_INTERVAL_SEC = 1.0
MAX_CARS           = 24
MIN_HEADWAY_PX     = 20

# Barrier animation (now rotates the correct way)
BARRIER_LEN        = 110
BARRIER_DOWN_ANG   = 0        # 0° = horizontal, blocking (extends LEFT across road)
BARRIER_UP_ANG     = 80       # +80° = raised (swings up)
BARRIER_SWING_DPS  = 180      # deg/sec

# Flashing lights
FLASH_HZ           = 1.2

# ===================== Pygame setup ===========================
pygame.init()
screen = pygame.display.set_mode((WIDTH, HEIGHT))
pygame.display.set_caption("Railway Level Crossing Safety System — Multi-Car (Polished)")
clock = pygame.time.Clock()
font_small  = pygame.font.SysFont("Arial", 18)
font_normal = pygame.font.SysFont("Arial", 28, bold=True)

# Colors (pleasant palette)
SKY      = (225, 240, 255)
GROUND   = (210, 225, 210)
ROAD_ASP = (210, 210, 210)
RAIL     = (35, 35, 35)
SLEEPER  = (120, 85, 60)
WHITE    = (255, 255, 255)
BLACK    = (0, 0, 0)
RED      = (205, 40, 40)
RED_DARK = (160, 20, 20)
GREEN    = (40, 180, 70)
GREEN_D  = (35, 140, 55)
BLUE     = (40, 80, 210)
YELLOW   = (250, 220, 70)

# ===================== Controller & geometry ==================
geom = Geometry(road_x=ROAD_X, train_w=TRAIN_W, approach_margin=180)
ctl  = LevelCrossingController(geom)

# ===================== Simulation state =======================
train_x = -TRAIN_W
barrier_angle = BARRIER_UP_ANG      # start raised
flash_phase = 0.0

@dataclass
class Car:
    y: float
    speed_pps: float = CAR_SPEED_PPS

cars: List[Car] = []
time_since_spawn = 0.0

# ===================== Drawing helpers ========================
def draw_round_rect(surf, rect, color, radius=8):
    pygame.draw.rect(surf, color, rect, border_radius=radius)

def draw_shadow_rect(surf, rect, blur_alpha=40):
    shadow = pygame.Surface((rect[2], rect[3]), pygame.SRCALPHA)
    shadow.fill((0, 0, 0, blur_alpha))
    surf.blit(shadow, (rect[0]+2, rect[1]+2))

def draw_scene_background():
    # Sky
    screen.fill(SKY)
    # Ground
    pygame.draw.rect(screen, GROUND, (0, TRACK_Y + 80, WIDTH, HEIGHT - (TRACK_Y + 80)))
    # Road (vertical)
    pygame.draw.rect(screen, ROAD_ASP, (ROAD_X - 44, 0, 88, HEIGHT))
    pygame.draw.line(screen, BLACK, (ROAD_X-44, 0), (ROAD_X-44, HEIGHT), 3)
    pygame.draw.line(screen, BLACK, (ROAD_X+44, 0), (ROAD_X+44, HEIGHT), 3)
    # Track sleepers (ties)
    for x in range(-40, WIDTH + 40, 40):
        pygame.draw.rect(screen, SLEEPER, (x, TRACK_Y - 18, 26, 36))
    # Rails
    pygame.draw.line(screen, RAIL, (0, TRACK_Y-14), (WIDTH, TRACK_Y-14), 6)
    pygame.draw.line(screen, RAIL, (0, TRACK_Y+14), (WIDTH, TRACK_Y+14), 6)

def draw_train(x):
    # Body
    body_rect = pygame.Rect(int(x), TRACK_Y - TRAIN_H//2, TRAIN_W, TRAIN_H)
    draw_shadow_rect(screen, body_rect)
    draw_round_rect(screen, body_rect, BLUE, radius=10)
    # Cab (front)
    cab_w = 56
    cab_rect = pygame.Rect(int(x)+TRAIN_W-cab_w, TRACK_Y - TRAIN_H//2-6, cab_w, TRAIN_H+12)
    draw_round_rect(screen, cab_rect, (25, 60, 180), radius=10)
    # Windows
    for i in range(3):
        wx = int(x) + 20 + i*60
        wy = TRACK_Y - TRAIN_H//2 + 8
        draw_round_rect(screen, (wx, wy, 36, 18), (180, 220, 255), radius=4)
    # Headlight
    pygame.draw.circle(screen, YELLOW, (int(x)+TRAIN_W-12, TRACK_Y), 6)

def draw_car(car: Car):
    x = ROAD_X - CAR_W//2
    y = int(car.y)
    # Wheels
    pygame.draw.circle(screen, BLACK, (ROAD_X - CAR_W//2 + 10, y + CAR_H - 6), 6)
    pygame.draw.circle(screen, BLACK, (ROAD_X + CAR_W//2 - 10, y + CAR_H - 6), 6)
    # Body
    car_rect = pygame.Rect(x, y, CAR_W, CAR_H)
    draw_shadow_rect(screen, car_rect)
    draw_round_rect(screen, car_rect, GREEN, radius=8)
    # Roof & window
    roof = pygame.Rect(x+6, y+6,     CAR_W-12, 18)
    win  = pygame.Rect(x+9, y+12,    CAR_W-18, 16)
    draw_round_rect(screen, roof, GREEN_D, radius=6)
    draw_round_rect(screen, win,  (190, 230, 255), radius=4)

def draw_barrier(angle_deg: float, lights_on_left: bool, lights_on_right: bool):
    """
    Hinge at (ROAD_X+44, BARRIER_Y).
    Arm extends LEFT across the road when blocking.
    Angle 0 = horizontal (blocking), +80 = raised.
    """
    hinge_x = ROAD_X + 44
    hinge_y = BARRIER_Y

    # Post
    pygame.draw.rect(screen, BLACK,    (hinge_x-10, hinge_y-56, 12, 112))
    pygame.draw.rect(screen, RED_DARK, (hinge_x-8,  hinge_y-20,  8,  40))

    # Arm polygon (rotated rectangle) — local X points LEFT (negative)
    arm_len, arm_h = BARRIER_LEN, 10
    ang = radians(angle_deg)
    pts_local = [(0, -arm_h/2), (-arm_len, -arm_h/2), (-arm_len, arm_h/2), (0, arm_h/2)]
    rot = []
    for px, py in pts_local:
        rx = hinge_x + px*cos(ang) - py*sin(ang)
        ry = hinge_y + px*sin(ang) + py*cos(ang)
        rot.append((rx, ry))
    pygame.draw.polygon(screen, RED, rot)

    # White stripes along the arm (also leftwards)
    for i in range(0, arm_len, 20):
        sx0 = hinge_x + (-(i+4)) * cos(ang);  sy0 = hinge_y + (-(i+4)) * sin(ang)
        sx1 = hinge_x + (-(i+14)) * cos(ang); sy1 = hinge_y + (-(i+14)) * sin(ang)
        pygame.draw.line(screen, WHITE, (sx0, sy0), (sx1, sy1), 3)

    # Flashing lights (left & right of road)
    r = 9
    left_pos  = (ROAD_X - 58, TRACK_Y - 26)
    right_pos = (ROAD_X + 58, TRACK_Y - 26)
    pygame.draw.circle(screen, RED_DARK, left_pos,  r)
    pygame.draw.circle(screen, RED_DARK, right_pos, r)
    if lights_on_left:
        pygame.draw.circle(screen, RED, left_pos,  r)
    if lights_on_right:
        pygame.draw.circle(screen, RED, right_pos, r)

def hud_text(train_speed, car_speed, spawn_int, count):
    lines = [
        f"Train speed: {train_speed:.0f} px/s  (-/+)",
        f"Car speed:   {car_speed:.0f} px/s  (9/0)",
        f"Spawn every: {spawn_int:.2f}s  ([ / ])   Cars: {count}/{MAX_CARS}",
        f"'H' hazard (barrier fails) | 'F' toggle fail-safe | 'C' spawn one car"
    ]
    for i, text in enumerate(lines):
        s = font_small.render(text, True, BLACK)
        screen.blit(s, (10, HEIGHT - 60 + i*18))

# ===================== Physics / logic helpers =================
def car_over_tracks(y):
    top, bot = y, y + CAR_H
    return not (bot < TRACK_Y - 16 or top > TRACK_Y + 16)

def car_should_stop_at_barrier(y, barrier_down):
    stop_line = BARRIER_Y + 14
    near_barrier = (y + CAR_H) >= stop_line and (y < stop_line + 10)
    return barrier_down and near_barrier

def check_collision_with_train(train_x_val, car: Car, barrier_down):
    train_crossing = ctl.train_in_crossing_zone(int(train_x_val))
    return (not barrier_down) and train_crossing and car_over_tracks(car.y)

def maintain_headway(idx: int, new_y: float) -> float:
    if idx == 0:
        return new_y
    ahead = cars[idx - 1]
    min_allowed_y = ahead.y + CAR_H + MIN_HEADWAY_PX
    return max(new_y, min_allowed_y)

def spawn_car():
    if len(cars) >= MAX_CARS: return
    start_y = HEIGHT - 90 + (len(cars) % 3) * 8
    cars.append(Car(y=start_y))

# ===================== Main loop ==============================
def run():
    global train_x, TRAIN_SPEED_PPS, CAR_SPEED_PPS, SPAWN_INTERVAL_SEC
    global time_since_spawn, barrier_angle, flash_phase

    while True:
        dt = clock.tick(60) / 1000.0  # seconds/frame

        # Input
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit(); sys.exit()
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_h:
                    ctl.hazard_mode = not ctl.hazard_mode
                if event.key == pygame.K_f:
                    # Toggle fail-safe latch (forces barrier down until clear)
                    ctl.set_fail_safe(not getattr(ctl, "fail_safe_active", False))
                if event.key in (pygame.K_MINUS, pygame.K_KP_MINUS):
                    TRAIN_SPEED_PPS = max(30.0, TRAIN_SPEED_PPS - 10.0)
                if event.key in (pygame.K_EQUALS, pygame.K_PLUS, pygame.K_KP_PLUS):
                    TRAIN_SPEED_PPS = min(700.0, TRAIN_SPEED_PPS + 10.0)
                if event.key in (pygame.K_9, pygame.K_KP9):
                    CAR_SPEED_PPS = max(20.0, CAR_SPEED_PPS - 10.0)
                if event.key in (pygame.K_0, pygame.K_KP0):
                    CAR_SPEED_PPS = min(450.0, CAR_SPEED_PPS + 10.0)
                if event.key == pygame.K_LEFTBRACKET:
                    SPAWN_INTERVAL_SEC = max(0.25, SPAWN_INTERVAL_SEC - 0.1)
                if event.key == pygame.K_RIGHTBRACKET:
                    SPAWN_INTERVAL_SEC = min(5.0, SPAWN_INTERVAL_SEC + 0.1)
                if event.key == pygame.K_c:
                    spawn_car()

        # Background
        draw_scene_background()

        # Pre-close: distance margin from time budget
        ctl.geom.approach_margin = int(TRAIN_SPEED_PPS * T_CLOSE_SEC + SAFETY_BUFFER_PX)

        # Move train (loop)
        train_x += TRAIN_SPEED_PPS * dt
        if train_x > WIDTH:
            train_x = -TRAIN_W

        # Update controller (barrier command)
        ctl.update(int(train_x))

        # Smooth barrier animation toward commanded state (unless hazard mode)
        target_ang = BARRIER_DOWN_ANG if (ctl.barrier_down and not ctl.hazard_mode) else BARRIER_UP_ANG
        if barrier_angle < target_ang:
            barrier_angle = min(target_ang, barrier_angle + BARRIER_SWING_DPS * dt)
        elif barrier_angle > target_ang:
            barrier_angle = max(target_ang, barrier_angle - BARRIER_SWING_DPS * dt)

        # Flashing lights timing (alternate when down)
        flash_phase += dt * FLASH_HZ
        left_on  = int(flash_phase) % 2 == 0 and ctl.barrier_down
        right_on = int(flash_phase) % 2 == 1 and ctl.barrier_down

        # Draw train + barrier + lights
        draw_train(int(train_x))
        draw_barrier(barrier_angle, left_on, right_on)

        # Spawn cars over time
        time_since_spawn += dt
        if time_since_spawn >= SPAWN_INTERVAL_SEC:
            time_since_spawn = 0.0
            spawn_car()

        # Update cars (front to back) with headway & barrier stop
        cars.sort(key=lambda c: c.y)
        for idx, car in enumerate(cars):
            desired_y = car.y - car.speed_pps * dt
            if car_should_stop_at_barrier(desired_y, ctl.barrier_down):
                desired_y = car.y
            desired_y = maintain_headway(idx, desired_y)
            car.y = desired_y

        # Remove cars that exited
        cars[:] = [c for c in cars if c.y + CAR_H >= -4]

        # Draw cars & check collisions
        collision = False
        for car in cars:
            if check_collision_with_train(train_x, car, ctl.barrier_down):
                collision = True
            draw_car(car)

        # Status banner
        if collision:
            banner = font_normal.render("⚠️  COLLISION!  Unsafe state", True, RED)
        elif getattr(ctl, "fail_safe_triggered", False):
            banner = font_normal.render("Fail-safe: Barriers forced down", True, BLACK)
            ctl.fail_safe_triggered = False
        else:
            banner = font_normal.render("System operating safely", True, BLACK)
        screen.blit(banner, (WIDTH//2 - banner.get_width()//2, 14))

        # HUD
        hud_text(TRAIN_SPEED_PPS, CAR_SPEED_PPS, SPAWN_INTERVAL_SEC, len(cars))

        pygame.display.flip()

# For direct run
if __name__ == "__main__":
    run()
