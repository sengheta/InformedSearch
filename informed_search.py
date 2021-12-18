############################################################
# CIS 521: Informed Search Homework
############################################################

student_name = "Sarah Engheta"

############################################################
# Imports
############################################################

import random
import collections
import itertools
import math
import queue
import copy
import cProfile




############################################################
# Section 1: Tile Puzzle
############################################################

def create_tile_puzzle(rows, cols):
    res = [[(x * cols) + (i + 1) for i in range(cols)] for x in range(rows)]
    res[rows - 1][cols - 1] = 0
    return TilePuzzle(res)


class TilePuzzle(object):

    # Required
    def __init__(self, board):
        self.board = board
        self.rows = len(board)
        self.cols = len(board[0])

        for i in range(len(board)):
            if 0 in board[i]:
                empty_row = i
                empty_col = board[i].index(0)
        self.empty_tile = [empty_row, empty_col]

    def get_board(self):
        return self.board

    def perform_move(self, direction):
        row = self.empty_tile[0]
        col = self.empty_tile[1]

        if direction != "up" and direction != "down" and direction != "left" and direction != "right":
            return False
        if direction == "up" and self.empty_tile[0] > 0:
            swapped_tile = self.board[row - 1][col]
            self.empty_tile[0] = row - 1  # reset empty tile properties
            self.board[row - 1][col] = 0  # reset empty tile on board
            self.board[row][col] = swapped_tile
            return True

        if direction == "down" and self.empty_tile[0] < self.rows - 1:
            swapped_tile = self.board[row + 1][col]
            self.empty_tile[0] = row + 1  # reset empty tile properties
            self.board[row + 1][col] = 0  # reset empty tile on board
            self.board[row][col] = swapped_tile
            return True

        if direction == "left" and self.empty_tile[1] > 0:
            swapped_tile = self.board[row][col - 1]
            self.empty_tile[1] = col - 1  # reset empty tile properties
            self.board[row][col - 1] = 0  # reset empty tile on board
            self.board[row][col] = swapped_tile
            return True

        if direction == "right" and self.empty_tile[1] < self.cols - 1:
            swapped_tile = self.board[row][col + 1]
            self.empty_tile[1] = col + 1  # reset empty tile properties
            self.board[row][col + 1] = 0  # reset empty tile on board
            self.board[row][col] = swapped_tile
            return True

        return False

    def scramble(self, num_moves):
        for i in range(num_moves):
            move = random.choice(["up", "down", "left", "right"])
            self.perform_move(move)

    def is_solved(self):
        res = [[(x * self.cols) + (i + 1) for i in range(self.cols)] for x in range(self.rows)]
        res[self.rows - 1][self.cols - 1] = 0

        if self.board == res:
            return True
        else:
            return False

    def copy(self):
        res = copy.deepcopy(self.board)
        return TilePuzzle(res)

    def successors(self):
        all_moves = ["up", "down", "left", "right"]
        for move in all_moves:
            res = self.copy()
            if res.perform_move(move):
                yield move, res

    def iddfs_helper(self, limit, moves, visited):
        if self.is_solved():
            yield moves

        if len(moves) < limit:
            for (move, res) in self.successors():
                next_config = tuple(tuple(x) for x in res.board)

                if next_config not in visited:
                    path = copy.deepcopy(visited)
                    path.append(next_config)
                    visited.append(next_config)
                    for x in res.iddfs_helper(limit, moves + [move], path):
                        yield x

    def find_solutions_iddfs(self):
        step_limit = 1
        results = []

        while len(results) == 0:
            visited = []
            results = list(self.iddfs_helper(step_limit, [], visited))
            step_limit += 1
        for sol in results:
            yield sol

    def find_solution_a_star(self):
        opened = queue.PriorityQueue()

        came_from = dict()
        came_from[self] = None
        cost_so_far = 0
        closed = []
        starting_point = tuple([self.heuristic(), [], cost_so_far, self])
        opened.put(starting_point)  # queue contains heuristic, self object, moves, and cost so far

        while not opened.empty():
            q = opened.get()
            q_board = tuple(tuple(x) for x in q[3].get_board())

            if q_board in closed:
                continue
            else:
                closed.append(q_board)

            if q[3].is_solved():
                return q[1]

            for move, res in q[3].successors():
                new_board = tuple(tuple(x) for x in res.get_board())

                new_cost = q[2] + 1

                if new_board not in closed:
                    next_point = tuple([new_cost + res.heuristic(), q[1] + [move], new_cost, res])
                    opened.put(next_point)

    def heuristic(self):

        h = 0
        for i in range(self.rows):
            for j in range(self.cols):
                if self.board[i][j] != 0:
                    goal_row = (self.board[i][j] - 1) / self.cols
                    goal_col = (self.board[i][j] - 1) % self.cols

                    h += abs(i - goal_row) + abs(j - goal_col)
        return h


############################################################
# Section 2: Grid Navigation
############################################################
class GridPuzzle(object):

    # Required
    def __init__(self, start, goal, scene):
        self.scene = scene
        self.scene_rows = len(scene)
        self.scene_cols = len(scene[0])
        self.current_point = start
        self.goal_point = goal

        obstacles = []
        for x in range(self.scene_rows):
            for y in range(self.scene_cols):
                if self.scene[x][y]:
                    obstacles.append(tuple([x, y]))

        self.obstacles = obstacles

    def get_current_point(self):
        return self.current_point

    def get_goal_point(self):
        return self.goal_point

    def is_solved(self):
        return self.current_point == self.goal_point

    def copy(self):
        r1 = copy.deepcopy(self.current_point)
        return GridPuzzle(r1, self.goal_point, self.scene)

    def perform_move(self, direction):

        if direction != "up" and direction != "down" and direction != "left" and direction != "right" and \
                direction != "up-right" and direction != "up-left" and direction != "down-right" \
                and direction != "down-left":
            return False

        if direction == "up" and self.current_point[0] > 0 and \
                not self.scene[self.current_point[0] - 1][self.current_point[1]]:
            self.current_point = (self.current_point[0] - 1, self.current_point[1])
            return True

        if direction == "down" and self.current_point[0] < self.scene_rows - 1 and \
                not self.scene[self.current_point[0] + 1][self.current_point[1]]:
            self.current_point = (self.current_point[0] + 1, self.current_point[1])
            return True

        if direction == "right" and self.current_point[1] < self.scene_cols - 1 and \
                not self.scene[self.current_point[0]][self.current_point[1] + 1]:
            self.current_point = (self.current_point[0], self.current_point[1] + 1)
            return True

        if direction == "left" and self.current_point[1] > 0 and \
                not self.scene[self.current_point[0]][self.current_point[1] - 1]:
            self.current_point = (self.current_point[0], self.current_point[1] - 1)
            return True

        if direction == "up-right" and self.current_point[0] > 0 and self.current_point[1] < self.scene_cols - 1 and \
                not self.scene[self.current_point[0] - 1][self.current_point[1] + 1]:
            self.current_point = (self.current_point[0] - 1, self.current_point[1] + 1)
            return True

        if direction == "up-left" and self.current_point[0] > 0 and self.current_point[1] > 0 and \
                not self.scene[self.current_point[0] - 1][self.current_point[1] - 1]:
            self.current_point = (self.current_point[0] - 1, self.current_point[1] - 1)
            return True

        if direction == "down-right" and self.current_point[0] < self.scene_rows - 1 and self.current_point[
            1] < self.scene_cols - 1 and \
                not self.scene[self.current_point[0] + 1][self.current_point[1] + 1]:
            self.current_point = (self.current_point[0] + 1, self.current_point[1] + 1)
            return True

        if direction == "down-left" and self.current_point[0] < self.scene_rows - 1 and self.current_point[1] > 0 and \
                not self.scene[self.current_point[0] + 1][self.current_point[1] - 1]:
            self.current_point = (self.current_point[0] + 1, self.current_point[1] - 1)
            return True

        return False

    def successors(self):
        all_moves = ["up", "down", "left", "right", "up-left", "up-right", "down-left", "down-right"]
        for move in all_moves:
            res = self.copy()
            if res.perform_move(move):
                yield move, res

    def euclidean_dist(self):
        return math.sqrt((self.current_point[0] - self.goal_point[0]) ** 2 + \
                         (self.current_point[1] - self.goal_point[1]) ** 2)

    def find_solution_a_star(self):
        opened = queue.PriorityQueue()
        cost_so_far = 0
        closed = set()
        starting_point = (self.euclidean_dist(), cost_so_far,[], self)
        opened.put(starting_point)  # queue contains heuristic, moves, cost so far, self


        while not opened.empty():
            q = opened.get()

            point = q[3].get_current_point()

            if point in closed:
                continue

            else:
                closed.add(point)

            if q[3].is_solved():
                return q[2] + [q[3].get_current_point()]

            for move, res in q[3].successors():
                new_point = res.get_current_point()

                if new_point not in closed:
                    if move == "up-left" or move == "down-left" or move == "up-right" or move == "down-right":
                        new_cost = q[1] + math.sqrt(2)
                        next_point = (new_cost + res.euclidean_dist(),new_cost, q[2] + [q[3].get_current_point()],  res)
                        opened.put(next_point)
                    else:
                        new_cost = q[1] + 1
                        next_point = (new_cost + res.euclidean_dist(),new_cost, q[2] + [q[3].get_current_point()],  res)
                        opened.put(next_point)
        return None

def find_path(start, goal, scene):
    p = GridPuzzle(start, goal, scene)
    return p.find_solution_a_star()


def main():
    scene = [[False, False, False],[False, True, False],[False, False, False]]
    print(find_path((0, 0), (2, 1), scene))


if __name__ == "__main__":
    main()


############################################################
# Section 3: Linear Disk Movement, Revisited
############################################################
class LinearDiscPuzzle(object):

    def __init__(self, board, n, length):
        self.length = length
        self.board = board
        self.n = n
        self.zeroes = self.length - n

    def get_board(self):
        return self.board

    def perform_move(self, fro, to):
        if to < 0 or to >= self.length:
            return False
        self.board[to] = self.board[fro]
        self.board[fro] = 0
        return True

    def is_solved_distinct(self):
        if any(self.board[:self.zeroes]) != 0:
            return False
        y = self.n
        for x in range(self.zeroes, self.length, 1):
            if self.board[x] != y:
                return False
            y -= 1
        return True

    def copy(self):
        return LinearDiscPuzzle(copy.deepcopy(self.board), self.n, self.length)

    def successors(self):

        for x in range(self.length):
            if self.board[x] == 0:
                continue

            if x + 1 < self.length and self.board[x + 1] == 0:
                res = self.copy()
                res.perform_move(x, x + 1)
                yield (x, x + 1), res

            if x + 2 < self.length and self.board[x + 2] == 0 and self.board[x + 1] != 0:
                res = self.copy()
                res.perform_move(x, x + 2)
                yield (x, x + 2), res

            if x - 1 >= 0 and self.board[x - 1] == 0:
                res = self.copy()
                res.perform_move(x, x - 1)
                yield (x, x - 1), res

            if x - 2 >= 0 and self.board[x - 2] == 0 and self.board[x - 1] != 0:
                res = self.copy()
                res.perform_move(x, x - 2)
                yield (x, x - 2), res

    def find_solution_distinct(self):
        frontier = queue.PriorityQueue()
        cost_so_far = 0

        starting_point = tuple([self.heuristic(),  cost_so_far,[], self])
        frontier.put(starting_point)
        closed = set()

        while True:
            if frontier.empty():
                return None

            p = frontier.get()
            point = tuple(p[3].get_board())

            if point in closed:
                continue
            else:
                closed.add(point)

            if p[3].is_solved_distinct():
                return p[2]

            for (step, new_p) in p[3].successors():

                new_board = tuple(new_p.get_board())
                if new_board in closed:
                    continue
                else:
                    new_cost = p[1] + 1
                    next_point = tuple(
                        [new_cost + new_p.heuristic(),new_cost, p[2] + [step],  new_p])
                    frontier.put(next_point)


        return None


    def heuristic(self):  # distance from current position to goal position for each disk
        h = 0
        for i in range(1,self.n):
            a = self.board.index(i)
            b = abs(self.length - 1 - a)
            if b >1:
                h+=2
            elif b == 0:
                h+=0
            else:
                h+=1
        return h


def create_puzzle_distinct(length, n):
    li = []
    for x in range(length):
        li.append(0)
    for i in range(n):
        li[i] = i + 1
    return li


def solve_distinct_disks(length, n):
    p = create_puzzle_distinct(length, n)
    grid = LinearDiscPuzzle(p, n, length)
    return grid.find_solution_distinct()

#
# def main():
#     print(solve_distinct_disks(9,6))
#
# if __name__ == "__main__":
#     cProfile.run('main()')

############################################################
# Section 4: Feedback
############################################################

# Just an approximation is fine.
feedback_question_1 = 40

feedback_question_2 = """
I find it extremely challenging to translate the theoretical frameworks and pseudocode taught in class 
actual code
"""

feedback_question_3 = """
The puzzles were interesting, I like the gamification of things for learning
"""
