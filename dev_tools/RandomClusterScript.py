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

        if int(attack[0]) <= cluster_size:
            attacker = arg_amount + 10

        if int(attack[1]) <= cluster_size:
            defender = arg_amount + 10

        if [attacker, defender] not in clustered_attacks:
            clustered_attacks.append([attacker, defender])
    return clustered_attacks



def generateFile(C_AF: list, inp_file: str, inp_folder: str, clustered_argument_amount: int, arg_amount: int, attackless: list):
    with open(f"{inp_folder}abstract/abstract_{inp_file[inp_file.find('_')+1:inp_file.find('.')]}.af", "w") as f:
        f.write(f"p af {arg_amount - clustered_argument_amount + 1}\n")
        f.write("# Clustered with Script\n")
        for attack in C_AF:
            f.write(f"{attack[0]} {attack[1]}\n")

        f.write("--cluster--\n")
        f.write(f"{arg_amount + 10} <- ")
        for i in range(1, clustered_argument_amount + 1):
            f.write(f"{i} ")

        attackless_final = list()
        if len(attackless) > 0:
            for arg in attackless:
                if int(arg) > clustered_argument_amount + 1:
                    attackless_final.append(arg)
        
        if len(attackless_final) > 0:
            f.write("\n--attackless--\n")
            for arg in attackless_final:
                f.write(f"{arg}\n")


        



def main():
    for file in os.listdir(f"{sys.argv[1]}/concrete"):
        arg_amount, attacks, attackless = readFile(sys.argv[1] + "concrete/" + file)
        cluster_size = int(random.randint(1, arg_amount))
        if int(cluster_size) > int(arg_amount):
            print("ERROR less arguments than cluster size")


        C_AF = clusterAF(attacks, arg_amount, cluster_size)
        generateFile(C_AF, file, sys.argv[1], cluster_size, arg_amount, attackless)
    print("Created", len(os.listdir(f"{sys.argv[1]}/concrete")), "abstracts af")



if __name__ == "__main__":
    main()