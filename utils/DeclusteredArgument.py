class DeclusteredArgument:
    def __init__(self, name: str, father_cluster: str) -> None:
        self.name = name
        self.father_cluster = father_cluster

    def __repr__(self) -> str:
        return f"DEC-ARG: {self.name}, f:{self.father_cluster}"
    