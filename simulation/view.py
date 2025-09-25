import pygame
from typing import Dict, List, Tuple
from math import cos, sin, radians

from .constants import (
    WIDTH, HEIGHT,
    TRACK_Y_TOP, TRACK_Y_BOT, TRACKS,
    ROAD_X, ROAD_HALF, POST_CLEAR,
    BARRIER_LEN,
    SKY, GROUND, ROAD_ASP, WHITE, BLACK, RED, RED_DARK,
    RAIL, SLEEPER, BLUE, GREEN, GREEN_D, YELLOW, ORANGE,
    NUM_LANES, LANE_W, CAR_W, CAR_H,
    SENSOR_A_X, SENSOR_B_X
)

# Fonts (init inside pygame-init context)
font_small  = None
font_normal = None
font_label  = None

def init_fonts():
    global font_small, font_normal, font_label
    font_small  = pygame.font.SysFont("Arial", 18)
    font_normal = pygame.font.SysFont("Arial", 28, bold=True)
    font_label  = pygame.font.SysFont("Arial", 14, bold=True)

def draw_round_rect(surf, rect, color, radius=8):
    pygame.draw.rect(surf, color, rect, border_radius=radius)

def draw_shadow_rect(surf, rect, blur_alpha=40):
    shadow = pygame.Surface((rect[2], rect[3]), pygame.SRCALPHA)
    shadow.fill((0, 0, 0, blur_alpha))
    surf.blit(shadow, (rect[0]+2, rect[1]+2))

def draw_lane_markings(screen):
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

def draw_scene_background(screen):
    screen.fill(SKY)
    pygame.draw.rect(screen, GROUND, (0, TRACK_Y_BOT + 120, WIDTH, HEIGHT - (TRACK_Y_BOT + 120)))

    # Road
    pygame.draw.rect(screen, ROAD_ASP, (ROAD_X - ROAD_HALF, 0, 2*ROAD_HALF, HEIGHT))
    pygame.draw.line(screen, BLACK, (ROAD_X-ROAD_HALF, 0), (ROAD_X-ROAD_HALF, HEIGHT), 3)
    pygame.draw.line(screen, BLACK, (ROAD_X+ROAD_HALF, 0), (ROAD_X+ROAD_HALF, HEIGHT), 3)
    draw_lane_markings(screen)

    # Tracks
    for ty in TRACKS:
        for x in range(-40, WIDTH + 40, 40):
            pygame.draw.rect(screen, SLEEPER, (x, ty - 18, 26, 36))
        pygame.draw.line(screen, RAIL, (0, ty-14), (WIDTH, ty-14), 6)
        pygame.draw.line(screen, RAIL, (0, ty+14), (WIDTH, ty+14), 6)

def draw_sensors(screen):
    for ty in TRACKS:
        pygame.draw.rect(screen, ORANGE, (SENSOR_A_X-3, ty-22, 6, 44), border_radius=2)
        pygame.draw.rect(screen, ORANGE, (SENSOR_B_X-3, ty-22, 6, 44), border_radius=2)
    la = font_small.render("A-sensor", True, BLACK)
    lb = font_small.render("B-sensor", True, BLACK)
    screen.blit(la, (SENSOR_A_X-40, TRACK_Y_TOP-36))
    screen.blit(lb, (SENSOR_B_X+10, TRACK_Y_TOP-36))

def draw_train(screen, nose_x: float, y_center: int, direction: int, TRAIN_W=240, TRAIN_H=56):
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

def _draw_barrier_arm(screen, hinge_x, hinge_y, angle_deg, extend_positive=True):
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

def draw_barrier_line(screen, y_line: int,
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
    _draw_barrier_arm(screen, left_post_x,  y_line, left_angle,  extend_positive=True)   # left extends +x
    _draw_barrier_arm(screen, right_post_x, y_line, right_angle, extend_positive=False)  # right extends -x

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

def draw_car(screen, car_rect):
    draw_shadow_rect(screen, car_rect)
    draw_round_rect(screen, car_rect, GREEN, radius=8)
    roof = pygame.Rect(car_rect.x+6, car_rect.y+6,  CAR_W-12, 18)
    win  = pygame.Rect(car_rect.x+9, car_rect.y+12, CAR_W-18, 16)
    draw_round_rect(screen, roof, GREEN_D, radius=6)
    draw_round_rect(screen, win,  (190, 230, 255), radius=4)

def hud_text(screen, font_small, active_info: str, states: Dict[str, bool], time_to_next_train: float, time_to_next_car: float, car_count: int, MIN_HEADWAY_PX: int, CAR_SPEED_PPS: float, hazard: bool, fail_safe: bool):
    sA = "DOWN" if states["A"] else "UP"
    sB = "DOWN" if states["B"] else "UP"
    sC = "DOWN" if states["C"] else "UP"
    sD = "DOWN" if states["D"] else "UP"
    lines = [
        f"Train: {active_info}   Next train in: {time_to_next_train:.1f}s   Next car in: {time_to_next_car:.1f}s",
        f"Barriers  A:{sA}  B:{sB}  C:{sC}  D:{sD}",
        f"Cars: {car_count}  Headway/ln: {MIN_HEADWAY_PX}px  Car speed: {CAR_SPEED_PPS:.0f}px/s   (H hazard: {'ON' if hazard else 'OFF'}, F fail-safe: {'ON' if fail_safe else 'OFF'})",
    ]
    for i, txt in enumerate(lines):
        s = font_small.render(txt, True, BLACK)
        screen.blit(s, (10, HEIGHT - 70 + i*20))

def banner_surface(text_color, text, font_normal):
    return font_normal.render(text, True, text_color)
