from math import inf
import math
import re
import time
import signal
import json
import subprocess
import os
import pandas as pd
from datetime import datetime

from numpy import var
from pysat.solvers import Cadical195
import fileinput
from tabulate import tabulate
import webbrowser
import sys
from pysat.pb import PBEnc, EncType
import csv

# input variables in database ?? mertens 1
n = 25
m = 6
c = 25
val = 0
cons = 0
sol = 0
solbb = 0
type = 1

# Global variables for tracking results
best_result = None
current_instance_id = 0
start_time_global = 0

# Signal handler for graceful interruption
def handle_interrupt(signum, frame):
    print(f"\nReceived interrupt signal {signum}. Saving current best solution.")
    
    if best_result:
        result = best_result.copy()
        result['Status'] = 'TIMEOUT'
        result['Runtime'] = time.time() - start_time_global
    else:
        result = {
            'Instance': file_name1[current_instance_id][0] if current_instance_id < len(file_name1) else 'Unknown',
            'n': n,
            'm': m,
            'c': c,
            'Variables': 0,
            'SoftClauses': 0,
            'HardClauses': 0,
            'OptimalValue': 0,
            'Status': 'TIMEOUT',
            'Runtime': time.time() - start_time_global
        }
    
    # Save result as JSON for the controller to pick up
    # with open(f'results_incremental_cadical_{current_instance_id}.json', 'w') as f:
    #     json.dump(result, f)
    
    print(f"Results saved for instance {current_instance_id}")
    sys.exit(0)

# Register signal handlers
signal.signal(signal.SIGTERM, handle_interrupt)
signal.signal(signal.SIGINT, handle_interrupt)

#           0              1                2           3           4           5           6           7               8                   9
file = ["MITCHELL.IN2","MERTENS.IN2","BOWMAN.IN2","ROSZIEG.IN2","BUXEY.IN2","HESKIA.IN2","SAWYER.IN2","JAESCHKE.IN2","MANSOOR.IN2",
        "JACKSON.IN2","GUNTHER.IN2", "WARNECKE.IN2"]
#            9          10              11          12          13          14          15          16          17   
filename = file[3]

fileName = filename.split(".")

with open('official_task_power/'+fileName[0]+'.txt', 'r') as file:
    W = [int(line.strip()) for line in file]

neighbors = [[ 0 for i in range(n)] for j in range(n)]
reversed_neighbors = [[ 0 for i in range(n)] for j in range(n)]

visited = [False for i in range(n)]
toposort = []
clauses = []
time_list = []
adj = []
forward = [0 for i in range(n)]
var_map = {}
var_counter = 0
# W = [41, 13, 21, 24, 11, 11, 41, 32, 31, 25, 29, 25, 31, 3, 14, 37, 34, 6, 18, 35, 18, 19, 25, 40, 20, 20, 36, 23, 29, 48, 41, 20, 31, 25, 1]

def read_input():
    cnt = 0
    global n, adj, neighbors, reversed_neighbors, filename, time_list, forward
    with open('presedent_graph/' + filename, 'r') as f:
        for line in f:
            line = line.strip()
            if line:
                if cnt == 0:
                    n = int(line)
                elif cnt <= n: # type: ignore
                    time_list.append(int(line))
                else:
                    line = line.split(",")
                    if(line[0] != "-1" and line[1] != "-1"):
                        adj.append([int(line[0])-1, int(line[1])-1])
                        neighbors[int(line[0])-1][int(line[1])-1] = 1
                        reversed_neighbors[int(line[1])-1][int(line[0])-1] = 1
                    else:
                        break
                cnt = cnt + 1


def generate_variables(n,m,c):
    x = [[j*m+i+1 for i in range (m)] for j in range(n)]
    a = [[m*n + j*c + i + 1 for i in range (c)] for j in range(n)]
    s = []
    cnt = m*n + c*n + 1
    for j in range(n):
        tmp = []
        for i in range(c - time_list[j] + 1):
            tmp.append(cnt)
            cnt = cnt + 1
        s.append(tmp)
    return x, a, s

def dfs(v):
    visited[v] = True
    for i in range(n):
        if(neighbors[v][i] == 1 and visited[i] == False):
            dfs(i)
    toposort.append(v)
def preprocess(n,m,c,time_list,adj):
    earliest_start = [[-9999999 for _ in range(m)] for _ in range(n)]
    latest_start = [[99999999 for _ in range(m)] for _ in range(n)]
    ip1 = [[0 for _ in range(m)] for _ in range(n)]
    test_ip1 = [[0 for _ in range(m)] for _ in range(n)]
    ip2 = [[[0 for _ in range(c)] for _ in range(m)] for _ in range(n)]
    # Compute earliest possible starting date and assigned workstation
    for i in range(n):
        if not visited[i]:
            dfs(i)
    toposort.reverse()
    # print(toposort)
    for j in toposort:
        k = 0
        earliest_start[j][k] = 0
        for i in range(n):
            if neighbors[i][j] == 1:

                earliest_start[j][k] = max(earliest_start[j][k], earliest_start[i][k] + time_list[i])

                while(earliest_start[j][k] > c - time_list[j]):
                    ip1[j][k] = 1
                    # print('X '+str(j+1)+' '+str(k+1))
                    k = k + 1
                    earliest_start[j][k] = max(0, earliest_start[i][k] + time_list[i])

                if earliest_start[j][k] <= c - time_list[j] :
                    for t in range(earliest_start[j][k]):
                        
                        if(ip2[j][k][t] == 0):
                            # with open("output.txt", "a") as output_file: 
                            #     sys.stdout = output_file  
                            #     print(j+1, k+1, t, file=output_file) 
                            ip2[j][k][t] = 1
    toposort.reverse()
    for j in toposort:
        k = m-1
        latest_start[j][k] = c - time_list[j]
        for i in range(n):
            if(neighbors[j][i] == 1): 
                latest_start[j][k] = min(latest_start[j][k], latest_start[i][k] - time_list[j])
                while(latest_start[j][k] < 0):
                    ip1[j][k] = 1
                    # print('X '+str(j+1)+' '+str(k+1))
                    k = k - 1
                    latest_start[j][k] = min(c - time_list[j], latest_start[i][k] - time_list[j])
                
                if(latest_start[j][k] >= 0):
                        for t in range(latest_start[j][k] + 1, c):
                            
                            if(ip2[j][k][t] == 0):
                                # with open("output.txt", "a") as output_file: 
                                #     sys.stdout = output_file
                                #     print(j+1, k+1, t, file=output_file) 
                                ip2[j][k][t] = 1
    
    # sys.stdout = sys.__stdout__


    # for j in range(n):
    #     for k in range(m):
    #         for t in range(c):
                # if(ip1[j][k] == 1):
                #     continue
                # if(j == 11 or j == 14):
                #     print(f"task {j+1} in machine {k+1} time {t+1}: {ip2[j][k][t]}")
                # if(j == 0 and k == 2):
                #     print(f"task {j+1} in machine {k+1} time {t+1}: {ip2[j][k][t]}")
    # print(ip2)
    return ip1,ip2

def get_key(value):
    for key, value in var_map.items():
        if val == value:
            return key
    return None
def get_var(name, *args):
    global var_counter
    key = (name,) + args

    if key not in var_map:
        var_counter += 1
        var_map[key] = var_counter
    return var_map[key]

def set_var(var, name, *args):
    key = (name,) + args
    if key not in var_map:
        var_map[key] = var
    return var_map[key]

def generate_clauses(n,m,c,time_list,adj,ip1,ip2,X,S,A):
    # #test
    # clauses.append([X[11 - 1][2 - 1]])
    global clauses
    global var_map
    global var_counter
    #staircase constraints
    for j in range(n):
        
        set_var(X[j][0], "R", j, 0)
        for k in range(1,m-1):
            if ip1[j][k] == 1:
                set_var(get_var("R", j, k-1), "R", j, k)
            else:
                clauses.append([-get_var("R", j, k-1), get_var("R", j, k)])
                clauses.append([-X[j][k], get_var("R", j, k)])
                clauses.append([-X[j][k], -get_var("R", j, k-1)])
                clauses.append([X[j][k], get_var("R", j, k-1), -get_var("R", j, k)])
        # last machine
        if ip1[j][m-1] == 1:
            clauses.append([get_var("R", j, m-2)])
        else:
            clauses.append([get_var("R", j, m-2), X[j][m-1]])
            clauses.append([-get_var("R", j, m-2), -X[j][m-1]])
        

    for (i,j) in adj:
        for k in range(m-1):
            if ip1[i][k+1] == 1:
                continue
            clauses.append([-get_var("R", j, k), -X[i][k+1]])
    # # 1
    # for j in range (0, n):
    #     # if(forward[j] == 1):
    #     #     continue
    #     constraint = []
    #     for k in range (0, m):
    #         if ip1[j][k] == 1:
    #             continue
    #         constraint.append(X[j][k])
    #     clauses.append(constraint)
    # # 2 
    # for j in range(0,n):
    #     # if(forward[j] == 1):
    #     #     continue
    #     for k1 in range (0,m-1):
    #         for k2 in range(k1+1,m):
    #             if ip1[j][k1] == 1 or ip1[j][k2] == 1:
    #                 continue
    #             clauses.append([-X[j][k1], -X[j][k2]])

    # #3
    # for a,b in adj:
    #     for k in range (0, m-1):
    #         for h in range(k+1, m):
    #             if ip1[b][k] == 1 or ip1[a][h] == 1:
    #                 continue
    #             clauses.append([-X[b][k], -X[a][h]])


    print("first 3 constraints (staircase):", len(clauses))

    # T[j][t] represents "task j starts at time t or earlier"
    for j in range(n):
        last_t = c-time_list[j]
        
        # Special case: Full cycle tasks (only one feasible start time: t=0)
        if last_t == 0:
            # Force the task to start at t=0 (equivalent to original constraint #4)
            clauses.append([S[j][0]])
        else:
            # First time slot
            set_var(S[j][0], "T", j, 0)
            
            # Intermediate time slots
            for t in range(1, last_t):
                clauses.append([-get_var("T", j, t-1), get_var("T", j, t)]) # T[j][t-1] -> T[j][t]
                clauses.append([-S[j][t], get_var("T", j, t)]) # S[j][t] -> T[j][t]
                clauses.append([-S[j][t], -get_var("T", j, t-1)]) # S[j][t] -> ¬T[j][t-1]
                clauses.append([S[j][t], get_var("T", j, t-1), -get_var("T", j, t)]) # T[j][t] -> (T[j][t-1] ∨ S[j][t])
            
            # Last time slot (ensures at least one start time)
            clauses.append([get_var("T", j, last_t-1), S[j][last_t]])
            clauses.append([-get_var("T", j, last_t-1), -S[j][last_t]])
    
    # Original constraints #4 and #5 
    # #4
    # for j in range(n):
    #     clauses.append([S[j][t] for t in range (c-time_list[j]+1)])

    # #5
    # for j in range(n):
    #     for k in range(c-time_list[j]):
    #         for h in range(k+1, c-time_list[j]+1):
    #             clauses.append([-S[j][k], -S[j][h]])

    # #6
    # for j in range(n):
    #     for t in range(c-time_list[j]+1,c):
    #         if t > c- time_list[j]:
    #             clauses.append([-S[j][t]])
    
    print("4 5 6 constraints (staircase):", len(clauses))

    #7
    for i in range(n-1):
        for j in range(i+1,n):
            for k in range (m):
                if ip1[i][k] == 1 or ip1[j][k] == 1 :
                    continue
                for t in range(c):
                    # if ip2[i][k][t] == 1 or ip2[j][k][t] == 1:
                    #     continue
                    clauses.append([-X[i][k], -X[j][k], -A[i][t], -A[j][t]])
    print("7 constraints:", len(clauses))
    #8
    for j in range(n):
        for t in range (c-time_list[j]+1):
            for l in range (time_list[j]):
                if(time_list[j] >= c/2 and t+l >= c-time_list[j] and t+l < time_list[j]):
                    continue
                clauses.append([-S[j][t],A[j][t+l]])
    
    print("8 constraints:", len(clauses))

    # addtional constraints
    # a task cant run before its active time

    # for j in range(n):
    #     for t in range (c-time_list[j]+1):
    #         for l in range (t):
    #             if(time_list[j] >= c/2 and l >= c-time_list[j] and l < time_list[j]):
    #                 continue
    #             clauses.append([-S[j][t],-A[j][l]])


    # addtional constraints option 2


    # for j in range(n):
    #     for t in range (c-1): 
    #         if(time_list[j] >= c/2 and t+1 >= c-time_list[j] and t+1 < time_list[j]):
    #             continue
    #         clauses.append([ -A[j][t], A[j][t+1] , S[j][max(0,t-time_list[j]+1)]])
    
    # #9

    for i,j in adj:
        for k in range(m):
            if ip1[i][k] == 1 or ip1[j][k] == 1:
                continue
            left_bound = time_list[i] - 1
            right_bound = c - time_list[j]
            clauses.append([-X[i][k], -X[j][k], -get_var("T", j, left_bound)])
            for t in range (left_bound + 1, right_bound):
                t_i = t - time_list[i]+1
                clauses.append([-X[i][k], -X[j][k], -get_var("T", j, t), -S[i][t_i]])
            for t in range (max(0,right_bound - time_list[i] + 1), c - time_list[i] + 1):
                clauses.append([-X[i][k], -X[j][k], -S[i][t], -get_var("T",j,c-time_list[j]-1)])
    # for i, j in adj:
    #     for k in range(m):
    #         if ip1[i][k] == 1 or ip1[j][k] == 1:
    #             continue
    #         for t1 in range(c - time_list[i] +1):
    #             #t1>t2
    #             for t2 in range(c-time_list[j]+1):
    #                 if ip2[i][k][t1] == 1 or ip2[j][k][t2] == 1:
    #                     continue
    #                 if t1 > t2:
    #                     clauses.append([-X[i][k], -X[j][k], -S[i][t1], -S[j][t2]])
    cons = len(clauses)
    print("Constraints:",cons)

    # #10
    for j in range(n):
        for k in range(m):
            if ip1[j][k] == 1:
                clauses.append([-X[j][k]])
                continue
                # print("constraint ", j+1, k+1)
            #11
            for t in range(c - time_list[j] +1):
                if ip2[j][k][t] == 1:
                    clauses.append([-X[j][k], -S[j][t]])
                    # print("constraint ", j+1, k+1, t)
    
    #12 
    for j in range(n):
        if(time_list[j] >= c/2):
            for t in range(c-time_list[j],time_list[j]):
                clauses.append([A[j][t]])
    print("12 constraints:", len(clauses))
    return clauses

class TimeoutException(Exception):
    pass

def timeout_handler(signum, frame):
    raise TimeoutException("Solver timeout")

def solve_with_timeout(solver, timeout_seconds):
    try:
        # Set up timeout signal
        signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(timeout_seconds)
        
        # Try to solve
        if solver.solve():
            result = solver.get_model()
        else:
            result = None
        
        # Cancel timeout if we finish early
        signal.alarm(0)
        return result
        
    except TimeoutException:
        signal.alarm(0)  # Cancel timeout
        print(f"Solver timed out after {timeout_seconds} seconds")
        return None

def solve(solver, start_time, timeout=3600):
    current_time = time.time()
    remaining_time = timeout - (current_time - start_time)
    
    if remaining_time <= 0:
        print("Timeout reached before calling solver")
        return None
    
    # Use signal-based timeout
    return solve_with_timeout(solver, int(remaining_time))

def save_solution_to_log(solution, best_value, instance_name, status=""):
    """Save solution to a date-based folder in log directory with instance-specific structure"""
    if solution is None:
        return None
    
    # Create date-based folder name
    current_date = datetime.now()
    date_folder = f"{current_date.day:02d}-{current_date.month:02d}-{current_date.year}"
    
    # Create instance-specific folder structure: log/date_folder/instance_name/n_m_c/
    instance_folder = os.path.join("log", date_folder, instance_name, f"{n}_{m}_{c}")
    
    # Create directory if it doesn't exist
    os.makedirs(instance_folder, exist_ok=True)
    
    # Generate solution data
    x = [[solution[j*m+i] for i in range(m)] for j in range(n)]
    a = [[solution[m*n + j*c + i] for i in range(c)] for j in range(n)]
    cnt = m*n + c*n 
    s = []
    for j in range(n):
        tmp = []
        for i in range(c - time_list[j] + 1):
            tmp.append(solution[cnt])
            cnt += 1
        s.append(tmp)
    
    table = [[0 for t in range(c)] for k in range(m)]
    for k in range(m):
        for t in range(c):
            for j in range(n):
                if x[j][k] > 0 and a[j][t] > 0 and table[k][t] == 0:
                    for l in range(max(0,t-time_list[j]),t+1):
                        if l < len(s[j]) and s[j][l] > 0:
                            table[k][t] = j+1

    # Generate task power list
    task_power_list = ""
    for j in range(n):
        task_power_list += f"task {j+1}: {W[j]}"
        if j < n-1:
            task_power_list += ", "
    
    # Generate task activity list with time ranges and machine assignments
    task_activities = []
    for j in range(n):
        # Find which machine this task is assigned to
        assigned_machine = -1
        for k in range(m):
            if x[j][k] > 0:
                assigned_machine = k + 1
                break
        
        if assigned_machine > 0:
            # Find the start and end times for this task
            start_time = -1
            end_time = -1
            for t in range(c):
                if a[j][t] > 0:
                    if start_time == -1:
                        start_time = t + 1  # Convert to 1-based indexing
                    end_time = t + 1  # Convert to 1-based indexing
                elif end_time > 0:
                    break
            
            if start_time > 0 and end_time > 0:
                task_activities.append(f"task {j+1} [{start_time};{end_time}] in machine {assigned_machine}")
    
    task_activities_text = ", ".join(task_activities)

    # Generate HTML content
    timestamp = current_date.strftime("%Y-%m-%d %H:%M:%S")
    html_content = f"""
    <!DOCTYPE html>
    <html>
    <head>
        <title>Task Assignment - {instance_name} ({n}_{m}_{c})</title>
        <style>
            body {{
                font-family: Arial, sans-serif;
                margin: 20px;
            }}
            table {{
                width: 100%;
                border-collapse: collapse;
                margin: 20px 0;
            }}
            table, th, td {{
                border: 1px solid black;
            }}
            th, td {{
                padding: 8px;
                text-align: center;
            }}
            th {{
                background-color: #f2f2f2;
            }}
            .info {{
                margin: 10px 0;
                line-height: 1.6;
            }}
            .best-value {{
                font-size: 18px;
                font-weight: bold;
                color: #2e7d32;
            }}
            .folder-path {{
                font-size: 12px;
                color: #666;
                margin-bottom: 10px;
            }}
            .detailed-info {{
                background-color: #f9f9f9;
                padding: 15px;
                border-radius: 5px;
                margin: 15px 0;
                border-left: 4px solid #2e7d32;
            }}
            .section-title {{
                font-weight: bold;
                color: #1976d2;
                margin-top: 10px;
            }}
        </style>
    </head>
    <body>
        <h2>Task Assignment - {instance_name}</h2>
        <div class="folder-path">
            <strong>Folder Structure:</strong> log/{date_folder}/{instance_name}/{n}_{m}_{c}/
        </div>
        
        <div class="detailed-info">
            <div class="section-title">Instance Details:</div>
            {instance_name}<br>
            n = {n}, m = {m}, c = {c}<br>
            
            <div class="section-title">Task Power Values:</div>
            {task_power_list}<br>
            
            <div class="section-title">Task Activities:</div>
            {task_activities_text}<br>
        </div>
        
        <div class="info">
            <p><strong>Timestamp:</strong> {timestamp}</p>
            <p><strong>Status:</strong> {status}</p>
            <p class="best-value">Best Value: {best_value}</p>
        </div>
        
        <h3>Task Assignment Table</h3>
        <table>
            <tr>
                <th>Machine</th>
                """ + "".join([f"<th>Time {t+1}</th>" for t in range(c)]) + """
            </tr>
    """

    for k in range(m):
        row = f"<tr><td>Machine {k+1}</td>" + "".join([f"<td>{table[k][t]}</td>" if table[k][t] > 0 else "<td></td>" for t in range(c)]) + "</tr>"
        html_content += row

    html_content += """
        </table>
    </body>
    </html>
    """

    # Save HTML file (without hour in filename, will replace if exists)
    html_filename = f"{instance_name}_bestvalue_{best_value}_{status}.html"
    html_filepath = os.path.join(instance_folder, html_filename)
    
    with open(html_filepath, "w") as file:
        file.write(html_content)
    
    # Also save raw solution data as JSON (without hour in filename, will replace if exists)
    solution_data = {
        'instance': instance_name,
        'configuration': f"{n}_{m}_{c}",
        'timestamp': timestamp,
        'best_value': best_value,
        'status': status,
        'parameters': {'n': n, 'm': m, 'c': c},
        'folder_structure': f"log/{date_folder}/{instance_name}/{n}_{m}_{c}/",
        'assignment_table': table,
        'x_variables': x,
        'a_variables': a,
        's_variables': s
    }
    
    json_filename = f"{instance_name}_bestvalue_{best_value}_{status}.json"
    json_filepath = os.path.join(instance_folder, json_filename)
    
    with open(json_filepath, "w") as file:
        json.dump(solution_data, file, indent=2)
    
    print(f"Solution saved to: {html_filepath}")
    print(f"Data saved to: {json_filepath}")
    print(f"Folder structure: log/{date_folder}/{instance_name}/{n}_{m}_{c}/")
    
    return html_filepath

def print_solution(solution):
    if solution is None:
        # print("No solution found.")
        return None
    else:
        x = [[solution[j*m+i] for i in range(m)] for j in range(n)]
        a = [[solution[m*n + j*c + i] for i in range(c)] for j in range(n)]
        # s = [[solution[m*n + c*n + j*c + i] for i in range(c)] for j in range(n)]
        cnt = m*n + c*n 
        s = []
        for j in range(n):
            tmp = []
            for i in range(c - time_list[j] + 1):
                tmp.append(solution[cnt])
                cnt += 1
            s.append(tmp)
        table = [[0 for t in range(c)] for k in range(m)]
        for k in range(m):
            for t in range(c):
                for j in range(n):
                    if x[j][k] > 0 and a[j][t] > 0 and table[k][t] == 0:
                        for l in range(max(0,t-time_list[j]),t+1):
                            if l < len(s[j]) and s[j][l] > 0:
                                table[k][t] = j+1

        # Generate HTML content
        html_content = """
        <!DOCTYPE html>
        <html>
        <head>
            <title>Task Assignment to Machines</title>
            <style>
                table {
                    width: 100%;
                    border-collapse: collapse;
                }
                table, th, td {
                    border: 1px solid black;
                }
                th, td {
                    padding: 8px;
                    text-align: center;
                }
                th {
                    background-color: #f2f2f2;
                }
            </style>
        </head>
        <body>
            <h2>Task Assignment to Machines</h2>
            <table>
                <tr>
                    <th>Machine</th>
                    """ + "".join([f"<th>Time {t+1}</th>" for t in range(c)]) + """
                </tr>
        """

        for k in range(m):
            row = f"<tr><td>Machine {k+1}</td>" + "".join([f"<td>{table[k][t]}</td>" if table[k][t] > 0 else "<td></td>" for t in range(c)]) + "</tr>"
            html_content += row

        html_content += """
            </table>
        </body>
        </html>
        """

        # Write HTML content to a file
        file_path = "task_assignment.html"
        with open(file_path, "w") as file:
            file.write(html_content)

        # Open the HTML file in the default web browser
        # webbrowser.open(file_path)

def get_value(solution,best_value):
    if solution is None:
        return 100, []
    else:
        x = [[  solution[j*m+i] for i in range (m)] for j in range(n)]
        a = [[  solution[m*n + j*c + i ] for i in range (c)] for j in range(n)]
        s = []
        cnt = m*n + c*n
        for j in range(n):
            tmp = []
            for i in range(c - time_list[j] + 1):
                tmp.append(solution[cnt])
                cnt += 1
            s.append(tmp)
        t = 0
        value = 0
        lowval = 0
        for t in range(c):
            tmp = 0
            for j in range(n):
                if a[j][t] > 0 :
                    # tmp = tmp + W[j]
                    for l in range(max(0,t-time_list[j]),t+1):
                        if l < len(s[j]) and s[j][l] > 0 :
                            tmp = tmp + W[j]
                            # print(tmp)
                            break
                
            if tmp > value:
                value = tmp
                # print(value)
            if tmp < lowval or lowval == 0:
                lowval = tmp
                # print("lowval:",lowval)
        constraints = []
        for t in range(c):
            tmp = 0
            station = []
            for j in range(n):
                if a[j][t] > 0:
                    # tmp = tmp + W[j]
                    # station.append(j+1)
                    for l in range(max(0,t-time_list[j]),t+1):
                        if l < len(s[j]) and s[j][l] > 0:
                            tmp = tmp + W[j]
                            station.append(j+1)
                            break
            if tmp >= min(best_value, value):
                constraints.append(station)
                # print("value:",value)
        unique_constraints = list(map(list, set(map(tuple, constraints))))

        return value, lowval, unique_constraints


def optimal(X,S,A,n,m,c,sol,solbb,start_time):
    global var_counter, var_map
    ip1,ip2 = preprocess(n,m,c,time_list,adj)

    # print(ip2[])


    clauses = generate_clauses(n,m,c,time_list,adj,ip1,ip2,X,S,A)

    solver = Cadical195()
    for clause in clauses:
        solver.add_clause(clause)

    model = solve(solver,start_time = start_time)
    if model is None:
        print("No solution found.")
        return 0, var_counter, clauses, "first cancelled"
    bestSolution = model 
    infinity = 1000000
    result = get_value(model, infinity)

    bestValue,lowval, station = result
    print("initial value:",bestValue)
    print("initial station:",station)
    # for t in range(c):
    #     for stations in station:
            
    #         solver.add_clause([-A[j-1][t] for j in stations])

    #∑(i∈{1,...,n}) w_i * A_{i,t} ≤ bestValue  ∀t∈T
    # for t in range(c):
    #     lits = []
    #     coeffs = []
    #     for j in range(n):
    #         lits.append(A[j][t])
    #         coeffs.append(W[j])
    #     pb_enc = PBEnc.leq(lits = lits, weights = coeffs, bound = bestValue - 1 , top_id = var_counter, encoding = EncType.binmerge)
    #     if pb_enc.nv > var_counter:
    #         var_counter = pb_enc.nv + 1
    #     for clause in pb_enc.clauses:
    #         solver.add_clause(clause)
    for t in range(c):
        for stations in station:
            solver.add_clause([-A[j-1][t] for j in stations])
    sol = 1
    solbb = 1
    while True:
        # start_time = time.time()
        sol = sol + 1
        model = solve(solver,start_time)
        if model is None:
            # print(bestSolution)
            return bestValue, var_counter, clauses, "Optimal"
        # solver = Cadical195()
        # for clause in clauses:
        #     solver.add_clause(clause)
        
        current_time = time.time()
        if current_time - start_time >= 3600:
            print("time out")
            return bestSolution, sol, solbb, bestValue
        # print(f"Time taken: {end_time - start_time} seconds")
        
        value,lowval, station = get_value(model, bestValue)
        # print("value:",value)
        # print("station:",station)
        if value < bestValue:
            solbb = sol
            bestSolution = model
            bestValue = value
            print("new value:",bestValue)
            # print("new station:",station)

        # for t in range(c):
        #     lits = []  
        #     coeffs = []
        #     for j in range(n):
        #         lits.append(A[j][t])
        #         coeffs.append(W[j])
        #     pb_enc = PBEnc.leq(lits = lits, weights = coeffs, bound = bestValue - 1 , top_id= var_counter + 1, encoding = EncType.binmerge)
        #     if pb_enc.nv > var_counter:
        #         var_counter = pb_enc.nv + 1
        #     for clause in pb_enc.clauses:
        #         solver.add_clause(clause)
        #         # print(stations)
        for t in range(c):
            for stations in station:
                solver.add_clause([-A[j-1][t] for j in stations])

def write_fancy_table_to_csv(ins, n, m, c, val, s_cons, h_cons, peak, status, time_elapsed, filename="staicase_time.csv"):
    global best_result
    
    # Create result dictionary
    result = {
        'Instance': ins,
        'n': n,
        'm': m,
        'c': c,
        'Variables': val,
        'SoftClauses': s_cons,
        'HardClauses': h_cons,
        'OptimalValue': peak,
        'Status': status,
        'Runtime': time_elapsed
    }
    
    # Update best result
    best_result = result.copy()
    
    # Write to CSV
    with open("Output/" + filename, "a", newline='') as f:
        writer = csv.writer(f)
        row = []
        row.append(ins)
        row.append(str(n))
        row.append(str(m))
        row.append(str(c))
        row.append(str(val))
        row.append(str(s_cons))
        row.append(str(h_cons))
        row.append(str(peak))
        row.append(status)
        row.append(str(time_elapsed))
        writer.writerow(row)

file_name1 = [
    # Easy families 
    # MERTENS 
    ["MERTENS", 6, 6],      # 0
    ["MERTENS", 2, 18],     # 1
    ["MERTENS", 5, 7],      # 2
    ["MERTENS", 5, 8],      # 3
    ["MERTENS", 3, 10],     # 4
    ["MERTENS", 2, 15],     # 5
    # Easy/MERTENS count: 6

    # BOWMAN
    ["BOWMAN", 5, 20],      # 6
    # Easy/BOWMAN count: 1

    # JAESCHKE
    ["JAESCHKE", 8, 6],     # 7
    ["JAESCHKE", 3, 18],    # 8
    ["JAESCHKE", 6, 8],     # 9
    ["JAESCHKE", 4, 10],    # 10
    ["JAESCHKE", 3, 18],    # 11
    # Easy/JAESCHKE count: 5

    # JACKSON
    ["JACKSON", 8, 7],      # 12
    ["JACKSON", 3, 21],     # 13
    ["JACKSON", 6, 9],      # 14
    ["JACKSON", 5, 10],     # 15
    ["JACKSON", 4, 13],     # 16
    ["JACKSON", 4, 14],     # 17
    # Easy/JACKSON count: 6

    # MANSOOR
    ["MANSOOR", 4, 48],     # 18
    ["MANSOOR", 2, 94],     # 19
    ["MANSOOR", 3, 62],     # 20
    # Easy/MANSOOR count: 3

    # MITCHELL
    ["MITCHELL", 8, 14],    # 21
    ["MITCHELL", 3, 39],    # 22
    ["MITCHELL", 8, 15],    # 23
    ["MITCHELL", 5, 21],    # 24
    ["MITCHELL", 5, 26],    # 25
    ["MITCHELL", 3, 35],    # 26
    # Easy/MITCHELL count: 6

    # ROSZIEG
    ["ROSZIEG", 10, 14],    # 27
    ["ROSZIEG", 4, 32],     # 28
    ["ROSZIEG", 6, 25],     # 29
    ["ROSZIEG", 8, 16],     # 30
    ["ROSZIEG", 8, 18],     # 31
    ["ROSZIEG", 6, 21],     # 32
    # Easy/ROSZIEG count: 6

    # HESKIA
    ["HESKIA", 8, 138],     # 33
    ["HESKIA", 3, 342],     # 34
    ["HESKIA", 5, 205],     # 35
    ["HESKIA", 5, 216],     # 36
    ["HESKIA", 4, 256],     # 37
    ["HESKIA", 4, 324],     # 38
    # Easy/HESKIA count: 6

    # Easy families total count: 39

    # Hard families
    # BUXEY
    ["BUXEY", 7, 47],       # 40
    ["BUXEY", 8, 41],       # 41
    ["BUXEY", 11, 33],      # 42
    ["BUXEY", 13, 27],      # 43
    ["BUXEY", 12, 30],      # 44
    ["BUXEY", 7, 54],       # 45
    ["BUXEY", 10, 36],      # 46
    # Hard/BUXEY count: 7

    # SAWYER
    ["SAWYER", 14, 25],     # 47
    ["SAWYER", 7, 47],      # 48
    ["SAWYER", 8, 41],      # 49
    ["SAWYER", 12, 30],     # 50
    ["SAWYER", 13, 27],     # 51
    ["SAWYER", 11, 33],     # 52
    ["SAWYER", 10, 36],     # 53 ???
    ["SAWYER", 7, 54],      # 54
    ["SAWYER", 5, 75],      # 55
    # Hard/SAWYER count: 9

    # GUNTHER
    ["GUNTHER", 9, 54],     # 57
    ["GUNTHER", 9, 61],     # 58
    ["GUNTHER", 14, 41],    # 59
    ["GUNTHER", 12, 44],    # 60
    ["GUNTHER", 11, 49],    # 61
    ["GUNTHER", 8, 69],     # 62
    ["GUNTHER", 7, 81],     # 63
    # Hard/GUNTHER count: 7

    # WARNECKE
    ["WARNECKE", 25, 65],   # 64
    ["WARNECKE", 31, 54],   # 65
    ["WARNECKE", 29, 56],   # 66
    ["WARNECKE", 29, 58],   # 67 
    ["WARNECKE", 27, 60],   # 68
    ["WARNECKE", 27, 62],   # 69
    ["WARNECKE", 24, 68],   # 70
    ["WARNECKE", 23, 71],   # 71
    ["WARNECKE", 22, 74],   # 72
    ["WARNECKE", 21, 78],   # 73
    ["WARNECKE", 20, 82],   # 74
    ["WARNECKE", 19, 86],   # 75
    ["WARNECKE", 17, 92],   # 76
    ["WARNECKE", 17, 97],   # 77
    ["WARNECKE", 15, 104],  # 78
    ["WARNECKE", 14, 111],  # 79
    # Hard/WARNECKE count: 16

    # Lutz2
    ["LUTZ2", 49, 11],      # 80
    ["LUTZ2", 44, 12],      # 81
    ["LUTZ2", 40, 13],      # 82
    ["LUTZ2", 37, 14],      # 83
    ["LUTZ2", 34, 15],      # 84
    ["LUTZ2", 31, 16],      # 85
    ["LUTZ2", 29, 17],      # 86
    ["LUTZ2", 28, 18],      # 87
    ["LUTZ2", 26, 19],      # 88
    ["LUTZ2", 25, 20],      # 89
    ["LUTZ2", 24, 21],      # 90
    # Hard/Lutz2 count: 11

    # Hard families total count: 50

    # Total: 89
]

def reset(idx):
    global n, m, c, val, cons, sol, solbb, type, filename, W, neighbors, reversed_neighbors, visited, toposort, clauses, time_list, adj, forward, var_map, var_counter, current_instance_id
    current_instance_id = idx
    m = file_name1[idx][1]
    c = file_name1[idx][2]
    val = 0
    cons = 0
    sol = 0
    solbb = 0
    type = 1
    var_counter = 0
    var_map = {}
    filename = file_name1[idx][0] + ".IN2"
    W = [int(line.strip()) for line in open('official_task_power/'+file_name1[idx][0]+'.txt')]
    neighbors = [[ 0 for i in range(200)] for j in range(200)]
    reversed_neighbors = [[ 0 for i in range(200)] for j in range(200)]
    visited = [False for i in range(200)]
    toposort = []
    clauses = []
    time_list = []
    adj = []
    forward = [0 for i in range(200)]

def run_single_instance(instance_id):
    """Run a single instance by ID"""
    global start_time_global, best_result, n, m, c, val, cons, sol, solbb, type, filename, W, neighbors, reversed_neighbors, visited, toposort, clauses, time_list, adj, forward, var_map, var_counter
    
    if instance_id >= len(file_name1):
        print(f"Invalid instance ID: {instance_id}. Max ID is {len(file_name1)-1}")
        return
    
    print(f"\nProcessing instance {instance_id}: {file_name1[instance_id][0]}")
    
    start_time_global = time.time()
    reset(instance_id)
    read_input()
    X, A, S = generate_variables(n,m,c)
    val = max(S)

    var_counter = max(val)
    var_map = {}

    sol = 0
    solbb = 0
    start_time = time.time()
    solval, vari, clauses, status = optimal(X,S,A,n,m,c,sol,solbb,start_time)
    end_time = time.time()
    
    # Write results
    write_fancy_table_to_csv(filename.split(".")[0], n, m, c, vari, 0, len(clauses), solval, status, end_time - start_time)
    
    # Save JSON result for controller
    # if best_result:
    #     with open(f'results_incremental_cadical_{instance_id}.json', 'w') as f:
    #         json.dump(best_result, f)
    
    print(f"Instance {instance_id} completed - Runtime: {end_time - start_time:.2f}s, Status: {status}")

if __name__ == "__main__":
    # Help message
    if len(sys.argv) > 1 and sys.argv[1] in ['-h', '--help', 'help']:
        print("Usage:")
        print("  python3 incremental_cadical_timeout.py              # Run all instances with runlim")
        print("  python3 incremental_cadical_timeout.py <id>         # Run single instance by ID")
        print("  python3 incremental_cadical_timeout.py easy         # Run only easy instances (0-38)")
        print("  python3 incremental_cadical_timeout.py hard         # Run only hard instances (39+)")
        print("  python3 incremental_cadical_timeout.py all          # Run all instances")
        print("")
        print(f"Available instances: {len(file_name1)} total")
        print("Easy instances: 0-38 (39 instances)")
        print("Hard instances: 39+ (remaining instances)")
        print("")
        print("Files created:")
        print("  Output/staicase_time.csv   # CSV results")
        print("  Output/Incremental_cadical_all.xlsx  # Excel results")
        print("  results_incremental_cadical_<id>.json # Individual results")
        print("")
        print("Optional timeout file: incremental_cadical_timeout.txt")
        print("  (List instance names to run only those instances)")
        sys.exit(0)
    
    # Check for special arguments
    if len(sys.argv) > 1 and sys.argv[1] in ['easy', 'hard', 'all']:
        difficulty = sys.argv[1]
        if difficulty == 'easy':
            # Only run easy instances (first 39)
            instances_to_run = file_name1[:39] if len(file_name1) >= 39 else file_name1
            print(f"Running EASY instances only: {len(instances_to_run)} instances")
        elif difficulty == 'hard':
            # Only run hard instances (40-89)
            instances_to_run = file_name1[39:] if len(file_name1) > 39 else []
            print(f"Running HARD instances only: {len(instances_to_run)} instances")
        else:  # 'all'
            instances_to_run = file_name1
            print(f"Running ALL instances: {len(instances_to_run)} instances")
        
        # Run selected instances with controller mode
        file_name1 = instances_to_run
        sys.argv = [sys.argv[0]]  # Reset argv to trigger controller mode
    
    # Controller mode - run all instances with runlim
    if len(sys.argv) == 1:
        # Create Output folder if it doesn't exist
        if not os.path.exists('Output'):
            os.makedirs('Output')
        
        # Read existing Excel file to check completed instances
        excel_file = 'Output/pb_all_time.xlsx'
        csv_file = 'Output/staicase_time.csv'

        completed_instances = []

        
        # Set timeout (1 hour = 3600s)
        TIMEOUT = 3601
        
        print(f"Running {len(file_name1)} instances with {TIMEOUT}s timeout each")
        
        # Run all instances with runlim
        # Here
        for instance_id in range(0, len(file_name1)):
            instance_name = file_name1[instance_id][0]
            
            print(f"\n{'=' * 50}")
            print(f"Running instance {instance_id}: {instance_name} (m={file_name1[instance_id][1]}, c={file_name1[instance_id][2]})")
            print(f"{'=' * 50}")
            
            # # Clean up previous result files
            # for temp_file in [f'results_incremental_cadical_{instance_id}.json', 
            #                   f'checkpoint_incremental_cadical_{instance_id}.json']:
            #     if os.path.exists(temp_file):
            #         os.remove(temp_file)
            
            # Run instance with timeout
            command = f"./runlim -r {TIMEOUT} python3   staircase4_time.py {instance_id}"
            
            try:
                process = subprocess.Popen(command, shell=True)
                process.wait()
                time.sleep(1)
                
            #     # Check results
            #     result = None
                
            #     # if os.path.exists(f'results_incremental_cadical_{instance_id}.json'):
            #     #     with open(f'results_incremental_cadical_{instance_id}.json', 'r') as f:
            #     #         result = json.load(f)
                
            #     # Process results
            #     if result:
            #         print(f"Instance {instance_name} - Status: {result['Status']}")
            #         print(f"Optimal Value: {result['OptimalValue']}, Runtime: {result['Runtime']}")
                    
            #         # Convert JSON to Excel format
            #         if os.path.exists(excel_file):
            #             try:
            #                 existing_df = pd.read_excel(excel_file)
            #                 result_df = pd.DataFrame([result])
            #                 existing_df = pd.concat([existing_df, result_df], ignore_index=True)
            #             except:
            #                 existing_df = pd.DataFrame([result])
            #         else:
            #             existing_df = pd.DataFrame([result])
                    
            #         existing_df.to_excel(excel_file, index=False)
            #         print(f"Results saved to {excel_file}")
                # else:
                #     print(f"No results found for instance {instance_name}")
                    
            except Exception as e:
                print(f"Error running instance {instance_name}: {str(e)}")
            
            # # Clean up temp files
            # for temp_file in [f'results_incremental_cadical_{instance_id}.json', 
            #                   f'checkpoint_incremental_cadical_{instance_id}.json']:
            #     if os.path.exists(temp_file):
            #         os.remove(temp_file)
        
        print(f"\nAll instances completed. Results saved to {excel_file}")
    
    # Single instance mode
    else:
        instance_id = int(sys.argv[1])
        run_single_instance(instance_id)

