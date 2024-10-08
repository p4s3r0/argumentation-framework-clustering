import sys
import math
import random

out_path = "../input/experiment/grid-based/concrete"


class Grid:
    def __init__(self, amount) -> None:
        self.size = math.ceil(math.sqrt(amount))
        self.amount = amount
        self.data = self.createGrid(amount)



    def createGrid(self, amount):
        grid = list()
        i = 0
        for x in range(self.size):
            temp = list()
            for y in range(self.size):
                if i >= amount: break;
                temp.append(Singleton(str(i)))
                i += 1
            grid.append(temp)
            if i >= amount: return grid;



    def getGridIndex(self, num):
        row = (num // self.size)
        col = num % self.size 
        return self.data[row][col]



    def addAttacks(self, p):
        for line in self.data:
            for s in line:
                # attack to left:
                if int(s.name) % self.size != 0:
                    if random.random() < p:
                        s.attacks.append(int(s.name)-1)
                        attacks = self.getGridIndex(int(s.name)-1)
                        attacks.attacked_by.append(s.name)

                # attacks to right
                if int(s.name) % self.size < self.size-1 and int(s.name) < self.amount - 1:
                    if random.random() < p:
                        s.attacks.append(int(s.name)+1)
                        attacks = self.getGridIndex(int(s.name)+1)
                        attacks.attacked_by.append(s.name)


                # attack to bottom:
                if int(s.name) // self.size < self.size - 1 and int(s.name) + self.size < self.amount:
                    if random.random() < p:
                        s.attacks.append(int(s.name)+self.size)
                        attacks = self.getGridIndex(int(s.name)+self.size)
                        attacks.attacked_by.append(s.name)

                # attacks to top
                if int(s.name) > self.size-1:
                    if random.random() < p:
                        s.attacks.append(int(s.name)-self.size)
                        attacks = self.getGridIndex(int(s.name)-self.size)
                        attacks.attacked_by.append(s.name)



    # Just for printing to console. for adequate printing amount <= 100
    def print(self) -> None:
        '''Just for printing to console. '''
        if self.amount > 100:
            print("IF YOU WANT TO PRINT IT, DONT USE AMOUNT > 100")
            return;

        for line in self.data:
            upper_upper_row = ""
            upper_lower_row = ""
            for el in line:
                # skip leftest col. Always check attacks to the current ele left
                in_leftest_col = False
                if int(el.name) % self.size == 0:
                    in_leftest_col = True

                in_top_col = False
                if int(el.name) < self.size * (self.size - 1):
                    in_top_col = True


                # not in leftes col and not very very last item
                if not in_leftest_col and int(el.name) < self.amount:
                    # check attack to left
                    if int(el.name) - 1 in el.attacks:
                        print("←", end="")
                    else:
                        print(" ", end="")

                    # check attack to right, if not very last element
                    if int(el.name) in self.getGridIndex(int(el.name)-1).attacks:
                        print("→", end="")
                    else:
                        print(" ", end="")


                print(f"{int(el.name)+1: 3} ", end="")

                # not at first row and item below exists
                if in_top_col and int(el.name) + self.size < self.amount:

                    # check attack top
                    if int(el.name) in self.getGridIndex(int(el.name) + self.size).attacks:
                        upper_upper_row += "↑     "
                    else:
                        upper_upper_row += "      "

                    # check attack bottom
                    if int(el.name) + self.size in el.attacks:
                        upper_lower_row += "↓     "
                    else:
                        upper_lower_row += "      "

            print("\n ", upper_upper_row, end="")
            print("\n ", upper_lower_row)



class Singleton:
    def __init__(self, name) -> None:
        self.name = name
        self.attacks = []
        self.attacked_by = []

    def __str__(self) -> str:
        return self.name



def writeGridToAFFile(filename, grid, p):
    has_attack = list()
    with open(filename, "w") as f:
        f.write(f"p af {grid.amount}\n")
        f.write(f"# approach: grid-based\n")
        f.write(f"# arg_amount: {grid.amount}\n")
        f.write(f"# p: {p}\n")

        write_cache = list()
        for row in grid.data:
            for s in row:
                for a in s.attacks:
                    if (int(s.name)+1) not in has_attack: has_attack.append(int(s.name)+1)
                    if (int(a)+1) not in has_attack: has_attack.append(int(a)+1)
                    write_cache.append(f"{int(s.name)+1} {int(a)+1}\n")

        f.write(f"# att_amount: {len(write_cache)}\n")

        for w in write_cache:
            f.write(w)

        attackless_written = False
        for i in range(1, grid.amount+1):
            if i not in has_attack:
                if not attackless_written:
                    f.write("--attackless--\n")
                    attackless_written = True
                f.write(f"{i}\n")



def main():
    if len(sys.argv) != 3 and len(sys.argv) != 4:
        print("usage: python3 grid-based.py <arg_amount> <p> (<af_amount>)")
        exit()

    arg_amount = int(sys.argv[1])
    probability = float(sys.argv[2])

    af_amount = 1
    if len(sys.argv) == 4:
        af_amount = int(sys.argv[3])

    for i in range(af_amount):
        grid = Grid(int(sys.argv[1]))
        grid.addAttacks(float(sys.argv[2]))

        file_name = f"{out_path}/args-{arg_amount}-p-{int(probability*100)}-i-{i}.af"
        writeGridToAFFile(file_name, grid, probability)

    print(f"Generated {af_amount} concrete AFs.")




if __name__ == "__main__":
    main()