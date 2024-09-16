from colorama import Fore, Back, Style

INFO = f"{Style.BRIGHT + Fore.BLUE}[INFO ]{Style.RESET_ALL} ->   "

DEBUG = True


def SET_INFO_DEBUG(value: bool):
    global DEBUG
    DEBUG = value


def info(info: str) -> None:
    if not DEBUG: return
    print(f"{INFO}{info}")


def progress(val: str) -> None:
    if not DEBUG: return
    print(f"{INFO}{val}", end="\r")

def progress_end() -> None:
    if not DEBUG: return
    print()

def SolutionSets(semantic: str, sets: list, name: str = "") -> None:
    if not DEBUG: return;
    semantic_text = ""
    if semantic == "AD":
        semantic_text = "ADMISSIBLE"
    elif semantic == "CF":
        semantic_text = "CONFLICT-FREE"
    else:
        semantic_text = "STABLE"
    print(f"{INFO}{Style.BRIGHT}{semantic_text} SETS: {Style.RESET_ALL} {name}", end="")
    for set in sets:
        print("{", end="")
        for arg in set:
            print(arg.name, end=",")
        print("}, ", end="")
    print("")

