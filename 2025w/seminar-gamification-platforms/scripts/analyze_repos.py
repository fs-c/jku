#!/usr/bin/env python3

import subprocess
import os
import re
import csv
from pathlib import Path
from collections import defaultdict
from datetime import date # Added for date manipulation

# --- CONFIGURATION ---

# 1. Add your repositories as (Name, URL) tuples
REPOS_TO_ANALYZE = [
    ("gamification-engine", "https://github.com/ActiDoo/gamification-engine.git"),
    ("siete-valles", "https://github.com/jorgegorka/siete-valles.git"),
    ("UserInfuser", "https://github.com/nlake44/UserInfuser.git"),
    ("Gamification-Server", "https://github.com/devleague/Gamification-Server.git"),
    ("django-gamification", "https://github.com/mattjegan/django-gamification.git"),
    ("FlarumGamification", "https://github.com/FriendsOfFlarum/gamification.git"),
    ("gioco", "https://github.com/joaomdmoura/gioco.git"),
    ("HyperosloGamification", "https://github.com/hyperoslo/gamification.git"),
    ("moodle-block_xp", "https://github.com/FMCorz/moodle-block_xp.git"),
    ("score.js", "https://github.com/mulhoon/score.js.git"),
    ("laravel-gamify", "https://github.com/qcod/laravel-gamify.git"),
    ("yay", "https://github.com/sveneisenschmidt/yay.git"),
    ("GamificationEngine-Kinben", "https://github.com/InteractiveSystemsGroup/GamificationEngine-Kinben.git"),
    ("oasis", "https://github.com/isuru89/oasis.git"),
    ("level-up", "https://github.com/cjmellor/level-up.git"),
    ("Gamify", "https://github.com/GollaBharath/Gamify.git"),
    ("gamify-laravel", "https://github.com/pacoorozco/gamify-laravel.git"),
    ("honor", "https://github.com/jrmyward/honor.git"),
    ("php-gamify", "https://github.com/mediasoftpro/php-gamify.git"),
    ("horde", "https://github.com/horde-lord/horde.git"),
    ("Gamification-Framework", "https://github.com/rwth-acis/Gamification-Framework.git"),
]

# 2. Set the directory where repos will be cloned
CLONE_DIR = "git_analysis_repos"

# 3. Set the directory for CSV reports
OUTPUT_DIR = "../thesis/data/"

# 4. If True, all reports will start from the same month (the earliest
#    commit across all repos). If False, each repo starts on its own
#    first commit month.
ALIGN_START_DATES = True

# --- END CONFIGURATION ---

# Regex to parse the --shortstat output
INSERTIONS_RE = re.compile(r'(\d+) insertion[s]?\(\+\)')
DELETIONS_RE = re.compile(r'(\d+) deletion[s]?\(-\)')

def run_command(command, cwd):
    """Helper to run a subprocess command."""
    try:
        result = subprocess.run(
            command,
            cwd=cwd,
            check=True,
            capture_output=True,
            text=True,
            encoding='utf-8',
            errors='ignore'
        )
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f"Error running command: {' '.join(command)}\nError: {e.stderr}")
        return None
    except FileNotFoundError:
        print("Error: 'git' command not found. Please ensure Git is installed and in your PATH.")
        exit(1)

def clone_or_pull(repo_url, target_dir):
    """Clones or pulls a repository (default branch only)."""
    repo_name = repo_url.split('/')[-1].replace('.git', '')
    repo_path = target_dir / repo_name

    if repo_path.exists():
        print(f"Updating {repo_name}...")
        run_command(["git", "pull", "--rebase"], cwd=repo_path)
    else:
        print(f"Cloning {repo_name} (single branch)...")
        run_command(
            ["git", "clone", "--single-branch", repo_url, str(repo_path)], 
            cwd=target_dir
        )
    
    return repo_path

def parse_repo_log(repo_path):
    """Parses the git log for a single repository."""
    print(f"Analyzing log for {repo_path.name}...")
    
    git_log_command = [
        "git", "log",
        "--shortstat",
        "--date=format:%Y-%m-%d",
        "--pretty=format:COMMIT_DELIM|%ad|%ae"
    ]
    
    log_output = run_command(git_log_command, cwd=repo_path)
    
    if not log_output:
        return []

    commit_data = []
    
    commits = log_output.split("COMMIT_DELIM|")
    
    for commit_chunk in commits:
        if not commit_chunk.strip():
            continue
            
        parts = commit_chunk.split('\n', 1)
        
        try:
            header = parts[0].strip()
            date_str, author_email = header.split('|')
            
            stat_lines = parts[1] if len(parts) > 1 else ""
            
            insertions = 0
            deletions = 0
            
            insertions_match = INSERTIONS_RE.search(stat_lines)
            if insertions_match:
                insertions = int(insertions_match.group(1))
                
            deletions_match = DELETIONS_RE.search(stat_lines)
            if deletions_match:
                deletions = int(deletions_match.group(1))
                
            commit_data.append((date_str, author_email, insertions, deletions))
            
        except (ValueError, IndexError) as e:
            pass
            
    print(f"Found {len(commit_data)} commits for {repo_path.name}.")
    return commit_data

def aggregate_data(all_commits_data):
    """Aggregates all commit data by month (YYYY-MM-01)."""
    
    monthly_stats = defaultdict(lambda: {
        'commits': 0,
        'committers': set(),
        'insertions': 0,
        'deletions': 0
    })
    
    for date_str, email, insertions, deletions in all_commits_data:
        month_str = f"{date_str[0:7]}-01"
        
        monthly_stats[month_str]['commits'] += 1
        monthly_stats[month_str]['committers'].add(email)
        monthly_stats[month_str]['insertions'] += insertions
        monthly_stats[month_str]['deletions'] += deletions
        
    return monthly_stats

def fill_missing_months(sparse_data, start_date, end_date):
    """
    Creates a new dict with all months from start_date to end_date.
    Fills in 0-commit data for any missing months.
    """
    full_data = {}
    current_date = start_date
    
    while current_date <= end_date:
        month_key = current_date.strftime("%Y-%m-01")
        
        if month_key in sparse_data:
            full_data[month_key] = sparse_data[month_key]
        else:
            # Add an empty data point for this month
            full_data[month_key] = {
                'commits': 0,
                'committers': set(),
                'insertions': 0,
                'deletions': 0
            }
        
        # Move to the first day of the next month
        month = current_date.month
        year = current_date.year
        month += 1
        if month > 12:
            month = 1
            year += 1
        current_date = date(year, month, 1)
        
    return full_data

def write_csv(stats_dict, filename, period_name):
    """Writes the aggregated data to a CSV file."""
    
    print(f"Writing {filename}...")
    
    sorted_periods = sorted(stats_dict.keys())
    
    with open(filename, 'w', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        
        writer.writerow([
            period_name,
            "commit_count",
            "unique_committers",
            "lines_added",
            "lines_deleted",
            "total_changes"
        ])
        
        for period in sorted_periods:
            data = stats_dict[period]
            unique_committers = len(data['committers'])
            total_changes = data['insertions'] + data['deletions']
            
            writer.writerow([
                period,
                data['commits'],
                unique_committers,
                data['insertions'],
                data['deletions'],
                total_changes
            ])

def main():
    """
    Main execution.
    1. Clones/pulls all repos and gathers raw log data.
    2. Finds the global start date if alignment is on.
    3. Processes each repo, filling in missing months.
    4. Writes a separate CSV for each repo.
    """
    # Get the directory where this script is located
    script_dir = Path(__file__).parent.resolve()
    clone_dir_path = script_dir / CLONE_DIR
    output_dir_path = script_dir / OUTPUT_DIR
    
    clone_dir_path.mkdir(exist_ok=True)
    output_dir_path.mkdir(exist_ok=True)
    
    all_repo_data = {}
    global_min_date_str = None
    
    print("--- Phase 1: Cloning Repos and Parsing Logs ---")
    for human_name, repo_url in REPOS_TO_ANALYZE:
        print(f"\nProcessing {human_name}...")
        repo_path = clone_or_pull(repo_url, clone_dir_path)
        
        if not repo_path:
            print(f"Skipping {human_name} due to clone/pull error.")
            all_repo_data[human_name] = []
            continue
            
        commit_data = parse_repo_log(repo_path)
        all_repo_data[human_name] = commit_data
        
        # If this repo has commits, check if it has a new global minimum date
        if commit_data:
            local_min_date_str = min(c[0] for c in commit_data) # c[0] is date string
            if global_min_date_str is None or local_min_date_str < global_min_date_str:
                global_min_date_str = local_min_date_str

    print("\n--- Phase 2: Aggregating and Writing Reports ---")
    
    today = date.today()
    # Set the end date to the first of the current month
    repo_end_date = today.replace(day=1) 
    
    # Determine the global start date if alignment is on
    timeline_start_date = None
    if ALIGN_START_DATES and global_min_date_str:
        timeline_start_date = date.fromisoformat(global_min_date_str).replace(day=1)
        print(f"Global start date alignment is ON. All reports will start from {timeline_start_date.strftime('%Y-%m')}.")
    else:
        print("Global start date alignment is OFF. Each report will use its own start date.")

    # Process each repo
    for human_name, commit_data in all_repo_data.items():
        print(f"\nAggregating data for {human_name}...")
        
        monthly_stats_sparse = aggregate_data(commit_data)
        
        # Determine the start date for this specific repo
        repo_start_date = None
        if timeline_start_date:
            # Use the aligned global start date
            repo_start_date = timeline_start_date
        elif commit_data:
            # Alignment is off, use this repo's local start date
            local_min_date_str = min(c[0] for c in commit_data)
            repo_start_date = date.fromisoformat(local_min_date_str).replace(day=1)
        else:
            # No commits and no alignment, just show the current month
            repo_start_date = repo_end_date 
            
        # Fill in all months from this repo's start to the end date
        monthly_stats_full = fill_missing_months(
            monthly_stats_sparse, 
            repo_start_date, 
            repo_end_date
        )
        
        monthly_filename = output_dir_path / f"{human_name}_monthly.csv"
        write_csv(monthly_stats_full, monthly_filename, "date")

    print(f"\n✅ Analysis complete!")
    print(f"Reports saved to the '{output_dir_path}' directory.")

if __name__ == "__main__":
    main()