"""
Titre : Projet Informatique Fondamentale INFO-F302 2025-2026
Date : 13 novembre 2025 - 21 décembre 2025
Membres : K. Ayman 000545130, N. P. Christine 000531295, L. Min-Tchun 000590125
"""


from pysat.solvers  import Minicard
from pysat.formula  import CNF, IDPool
from pysat.card     import CardEnc


# Question 2
def gen_solution(durations: list[int], c: int, T: int) -> None | list[tuple]:
    """
    Args :
        - durations: list[int] ; liste des temps de traversée pour chaque poule
        - c: int ; capacité de la barque
        - T: int ; durée au plus T pour faire traverser toutes les poules

    Returns :
        /
    """

    n               = len(durations)    # Nombre de poules
    max_duration    = max(durations)    # Durée maximale d'une traversée

    vpool   = IDPool()          # Identification des variables utilisées
    cnf     = CNF()             # Stockage des clauses

    # Variables utilisées (cf. suggestions consignes et rapport)
    def dep(t, p, s): return vpool.id(("dep", t, p, s))

    def A(p, t): return vpool.id(("A", p, t))

    def B(p, t): return vpool.id(("B", p, t))

    def dur(t, d): return vpool.id(("dur", t, d))

    def side(t): return vpool.id(("side", t))

    def DEP(t): return vpool.id(("DEP", t))

    def ARR(t): return vpool.id(("ARR", t))

    def ALL(t): return vpool.id(("ALL", t))

    # Contrainte (1)
    for t in range(T + 1):
        clause = [-DEP(t)]

        for p in range(n):
            clause.append(dep(t, p, "Aller"))
            clause.append(dep(t, p, "Ret"))

            cnf.append([-dep(t, p, "Aller"), DEP(t)])
            cnf.append([-dep(t, p, "Ret"), DEP(t)])

        cnf.append(clause)

    # Contrainte (2)
    for t in range(T + 1):
        for d in range(max_duration + 1):
            cnf.append([DEP(t), -dur(t, d)])

    # Contrainte (3)
    for t in range(1, T + 1):
        # Première clause
        clause = [-ARR(t)]

        for u in range(t):
            for d in range(max_duration + 1):
                if u + d == t:
                    clause.append(dur(u, d))

        cnf.append(clause)

        # Deuxième clause
        for u in range(t):
            for d in range(max_duration + 1):
                if u + d == t:
                    cnf.append([-dur(u, d), ARR(t)])

    # Contrainte (4)
    for t in range(T + 1):
        for p in range(n):
            for q in range(n):
                cnf.append([-dep(t, p, "Aller"), -dep(t, q, "Ret")])

    # Contrainte (5)
    for t in range(T + 1):
        # Première clause
        for p in range(n):
            cnf.append([-ALL(t), B(p, t)])

        # Deuxième clause
        clause = [ALL(t)]

        for p in range(n):
            clause.append(-B(p, t))

        cnf.append(clause)

    # Contrainte (6)
    for p in range(n):
        cnf.append([A(p, 0)])
        cnf.append([-B(p, 0)])

    for t in range(T + 1):
        for p in range(n):
            cnf.append([-A(p, t), -B(p, t)])
            cnf.append([A(p, t), B(p, t)])

    # Contrainte (7)
    for t in range(T + 1):
        for d in range(max_duration + 1):
            for p in range(n):
                if durations[p] > d:
                    cnf.append([-dur(t, d), -dep(t, p, "Aller")])
                    cnf.append([-dur(t, d), -dep(t, p, "Ret")])

    # Contrainte (8)
    for t in range(T + 1):
        for d in range(max_duration + 1):
            clause = [-dur(t, d)]

            for p in range(n):
                if durations[p] == d:
                    clause.append(dep(t, p, "Aller"))
                    clause.append(dep(t, p, "Ret"))

            cnf.append(clause)

    # Contrainte (9)
    for t in range(T + 1):
        all_p = [] # Toutes les poules qui pourraient être dans la barque à un instant t

        for p in range(n):
            all_p.append(dep(t, p, "Aller"))
            all_p.append(dep(t, p, "Ret"))

        # cnf.extend ajoute toutes les clauses
        # CardEnc.atmost().clauses return une liste de clauses FNC
        # bound=c ; au plus c éléments peuvent être vrais
        cnf.extend(CardEnc.atmost(lits=all_p, bound=c, vpool=vpool, encoding=1).clauses)

    # Contrainte (10) -> équivalente à la contrainte (1)

    # Contrainte (11)
    for t in range(T + 1):
        for p in range(n):
            # Aller vers côté B ; barque est sur le côté A
            cnf.append([-dep(t, p, "Aller"), side(t)])

            # Retour vers côté A ; barque est sur le côté B
            cnf.append([-dep(t, p, "Ret"), -side(t)])

    # Contrainte (12)
    for t in range(T + 1):
        for d in range(max_duration + 1):
            """
            min(T + 1, t + d) ; T + 1 fin maximale autorisée, t + d fin théorique
            ex. : T = 10, t = 8, d = 5
            u appartient à {9, 10, 11, 12} mais 11 et 12 n'existent pas car T = 10
            """
            for u in range(t + 1, min(T + 1, t + d)):
                cnf.append([-dur(t, d), -DEP(u)])

    # Contrainte (13)
    for t in range(T):
        # S'il n'y a pas d'arrivée à l'instant t+1 alors le côté ne change pas
        cnf.append([ARR(t + 1), -side(t + 1), side(t)])
        cnf.append([ARR(t + 1), -side(t), side(t + 1)])

        # Inversement, s'il y a une arrivée à l'instant t+1 alors le côté change
        cnf.append([-ARR(t + 1), -side(t + 1), -side(t)])
        cnf.append([-ARR(t + 1), side(t), side(t + 1)])

    # Contrainte (14) - Contrainte (15) - Contrainte (16)
    for t in range(T + 1):
        for d in range(max_duration + 1):
            for p in range(n):
                # if t + d <= T ; ajout sur base de la réflexion pour la Contrainte (12)
                if t + d <= T:
                    # Partie contrainte (14)
                    cnf.append([-dur(t, d), -dep(t, p, "Aller"), A(p, t)])
                    cnf.append([-dur(t, d), -dep(t, p, "Aller"), B(p, t + d)])

                    # Partie contrainte (15)
                    cnf.append([-dur(t, d), -dep(t, p, "Ret"), B(p, t)])
                    cnf.append([-dur(t, d), -dep(t, p, "Ret"), A(p, t + d)])

                    # Partie contrainte (16)
                    cnf.append([-dur(t, d), dep(t, p, "Aller"), dep(t, p, "Ret"), -A(p, t), A(p, t + d)])
                    cnf.append([-dur(t, d), dep(t, p, "Aller"), dep(t, p, "Ret"), -A(p, t + d), A(p, t)])

    """
    Ajouts ci-dessous à mettre dans le rapport
    """
    # Barque est sur le côté A à l'instant t=0
    cnf.append([side(0)])

    # Toutes les poules sont sur le côté B à l'instant T
    cnf.append([ALL(T)])

    # Solveur 
    with Minicard(bootstrap_with=cnf) as solver :
        solution_exists = solver.solve()

        if solution_exists:
            model = solver.get_model()
            solution = []

            for t in range(T + 1):
                if DEP(t) in model:
                    chickens = []

                    for p in range(n):
                        if dep(t, p, "Aller") in model or dep(t, p, "Ret") in model:
                            chickens.append(p + 1)

                    if chickens:
                        solution.append((t, chickens))

            return solution

        else:
            return None


# Question 3
def find_duration(durations: list[int], c: int) -> int:
    n = len(durations)

    # Une seule poule
    if n == 1:
        return durations[0]

    min_duration = 0
    max_duration = 2 * sum(durations)

    while min_duration < max_duration:
        duration_test = (min_duration + max_duration) // 2

        if gen_solution(durations, c, duration_test) is not None:
            max_duration = duration_test
        else:
            min_duration = duration_test + 1

    return min_duration
