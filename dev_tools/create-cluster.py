import sys
import random
import os
'''
Creates a Clustered AF from the input file. The Cluster Contains 
<X> Singletons, where <X> is defined as command line argument.
the input format is the following:
input format: python3 RandomClusterScript.py <filename> <cluster_size>
'''


def readFile(filename: str):
    arg_amount= 0
    attacks=list()
    attackless=list()

    with open(filename, "r") as f: 
        arg_amount = int(f.readline().split()[2])
        attackless_check = False
        for attack in f:
            if attack == "--attackless--\n":
                attackless_check = True
                continue

            if attackless_check:
                attackless.append(attack.split()[0])
                continue

            if len(attack.split()) <= 0 or attack.split()[0] == '#':
                continue
            if len(attack.split()) != 2:
                print("ERROR", attack)

            if attack.split() not in attacks:
                attacks.append(attack.split())
    return arg_amount, attacks, attackless



def clusterAF(attacks: list, arg_amount: int, cluster_size: int):
    clustered_attacks = list()

    for attack in attacks:
        attacker = attack[0]
        defender = attack[1]

        if int(attacker) <= cluster_size:
            attacker = arg_amount + 10

        if int(defender) <= cluster_size:
            defender = arg_amount + 10

        if [attacker, defender] not in clustered_attacks:
            clustered_attacks.append([attacker, defender])
    return clustered_attacks



def generateFile(C_AF: list, inp_file: str, inp_folder: str, clustered_argument_amount: int, arg_amount: int, attackless: list, typeOfFile: str = "MULTIPLE"):
    file = ""
    if typeOfFile == "MULTIPLE":
        file = f"{inp_folder}abstract/{inp_file[inp_file.find('_')+1:inp_file.find('.')]}.af"
    else:
        file = f"{inp_file[inp_file.find('_')+1:inp_file.find('.')]}_abstract.af"

    with open(file, "w") as f:
        f.write(f"p af {arg_amount - clustered_argument_amount + 1}\n")
        f.write("# Clustered with Script\n")
        concretize_arguments = [random.randint(1, clustered_argument_amount)]
        for i in range(clustered_argument_amount - 3):
            rand_item = random.randint(1, clustered_argument_amount)
            if rand_item not in concretize_arguments:
                concretize_arguments.append(rand_item)
            if random.random() < 0.5:
                break;
        f.write(f"# concretize: ")
        for arg in concretize_arguments:
            f.write(f"{arg} ")
        f.write("\n")

        cluster_has_attack = False
        for attack in C_AF:
            if attack[0] == arg_amount + 10 or attack[1] == arg_amount + 10:
                cluster_has_attack = True
            f.write(f"{attack[0]} {attack[1]}\n")


        attackless_final = list()
        if not cluster_has_attack:
            attackless_final.append(arg_amount + 10)


        if len(attackless) > 0:
            for arg in attackless:
                if int(arg) > clustered_argument_amount + 1:
                    attackless_final.append(arg)


        if len(attackless_final) > 0:
            f.write("--attackless--\n")
            for arg in attackless_final:
                f.write(f"{arg}\n")


        f.write("--cluster--\n")
        f.write(f"{arg_amount + 10} <- ")
        for i in range(1, clustered_argument_amount + 1):
            f.write(f"{i} ")



def main():
    '''
    Folder structure:   dir/abstract/<empty>
                        dir/concrete/concrete_<num>.af
    '''
    dir = sys.argv[1]
    for file in os.listdir(f"{dir}/concrete"):
        arg_amount, attacks, attackless = readFile(dir + "concrete/" + file)
        cluster_size = int(random.randint(2, arg_amount))

        C_AF = clusterAF(attacks, arg_amount, cluster_size)
        generateFile(C_AF, file, dir, cluster_size, arg_amount, attackless)
    print("Created", len(os.listdir(f"{dir}/concrete")), "abstracts af")




if __name__ == "__main__":
    main()