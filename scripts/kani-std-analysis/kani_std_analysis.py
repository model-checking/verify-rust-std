#!/usr/bin/env python3

import argparse
from collections import defaultdict
import csv
import json
import sys
from datetime import datetime
import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from matplotlib.ticker import FixedLocator

# Output metrics about Kani's application to the standard library by:
#   1. Postprocessing results from running `kani list`, which collects data about Kani harnesses and contracts.
#   2. Postprocessing results from std-analysis.sh, which outputs metrics about the standard library unrelated to Kani (e.g., a list of the functions in each crate).
#   3. Comparing the output of steps #1 and #2 to compare the Kani-verified portion of the standard library to the overall library,
#      e.g., what fraction of unsafe functions have Kani contracts.
# Note that this script assumes that std-analysis.sh and `kani list` have already run, since we expect to invoke this script from `run-kani.sh`.
# Also note that the results are architecture-dependent: the standard library has functions that are only present for certain architectures, 
# and https://github.com/model-checking/verify-rust-std/pull/122 has Kani harnesses that only run on x86-64.

# Process the results from Kani's std-analysis.sh script for each crate.
# TODO For now, we just handle "core", but we should process all crates in the library.
class GenericSTDMetrics():
    def __init__(self):
        self.results_directory = "/tmp/std_lib_analysis/results"
        self.unsafe_fns_count = 0
        self.safe_abstractions_count = 0
        self.unsafe_fns = []
        self.safe_abstractions = []

        self.read_std_analysis()
        
    # Read {crate}_overall_counts.csv
    # and return the number of unsafe functions and safe abstractions
    def read_overall_counts(self):
        file_path = f"{self.results_directory}/core_scan_overall.csv"
        with open(file_path, 'r') as f:
            csv_reader = csv.reader(f, delimiter=';')
            counts = {row[0]: int(row[1]) for row in csv_reader if len(row) >= 2}
        self.unsafe_fns_count = counts.get('unsafe_fns', 0)
        self.safe_abstractions_count = counts.get('safe_abstractions', 0)

    # Read {crate}_scan_functions.csv
    # and return an array of the unsafe functions and the safe abstractions
    def read_scan_functions(self):
        expected_header_start = "name;is_unsafe;has_unsafe_ops"
        file_path = f"{self.results_directory}/core_scan_functions.csv"

        with open(file_path, 'r') as f:
            csv_reader = csv.reader(f, delimiter=';', quotechar='"')
            
            # The row parsing logic below assumes the column structure in expected_header_start,
            # so assert that is how the header begins before continuing
            header = next(csv_reader)
            header_str = ';'.join(header[:3])
            if not header_str.startswith(expected_header_start):
                print(f"Error: Unexpected CSV header in {file_path}")
                print(f"Expected header to start with: {expected_header_start}")
                print(f"Actual header: {header_str}")
                sys.exit(1)

            for row in csv_reader:
                if len(row) >= 3:
                    name, is_unsafe, has_unsafe_ops = row[0], row[1], row[2]
                    # An unsafe function is a function for which is_unsafe=true
                    if is_unsafe.strip() == "true":
                        self.unsafe_fns.append(name)
                    # A safe abstraction is a function that is not unsafe (is_unsafe=false) but has unsafe ops
                    elif is_unsafe.strip() == "false" and has_unsafe_ops.strip() == "true":
                        self.safe_abstractions.append(name)

    def read_std_analysis(self):
        self.read_overall_counts()
        self.read_scan_functions()

        # Sanity checks for the CSV parsing
        if len(self.unsafe_fns) != self.unsafe_fns_count:
            print(f"Number of unsafe functions does not match core_scan_functions.csv")
            print(f"UNSAFE_FNS_COUNT: {self.unsafe_fns_count}")
            print(f"UNSAFE_FNS length: {len(self.unsafe_fns)}")
            sys.exit(1)

        if len(self.safe_abstractions) != self.safe_abstractions_count:
            print(f"Number of safe abstractions does not match core_scan_functions.csv")
            print(f"SAFE_ABSTRACTIONS_COUNT: {self.safe_abstractions_count}")
            print(f"SAFE_ABSTRACTIONS length: {len(self.safe_abstractions)}")
            sys.exit(1)

# Process the results of running `kani list` against the standard library,
# i.e., the Kani STD metrics for a single date (whichever day this script is running).
class KaniListSTDMetrics():
    def __init__(self, kani_list_filepath):
        self.total_fns_under_contract = 0
        # List of (fn, has_harnesses) tuples, where fn is a function under contract and has_harnesses=true iff the contract has at least one harness
        self.fns_under_contract = []
        self.expected_kani_list_version = "0.1"

        self.read_kani_list_data(kani_list_filepath)

    def read_kani_list_data(self, kani_list_filepath):
        try:
            with open(kani_list_filepath, 'r') as f:
                kani_list_data = json.load(f)
        except FileNotFoundError:
            print(f"Kani list JSON file not found.")
            sys.exit(1)
        
        if kani_list_data.get("file-version") != self.expected_kani_list_version:
            print(f"Kani list JSON file version does not match expected version {self.expected_kani_list_version}")
            sys.exit(1)

        for contract in kani_list_data.get('contracts', []):
            func_under_contract = contract.get('function', '')
            has_harnesses = len(contract.get('harnesses', [])) > 0
            self.fns_under_contract.append((func_under_contract, has_harnesses))

        self.total_fns_under_contract = kani_list_data.get('totals', {}).get('functions-under-contract', 0)

# Generate metrics about Kani's application to the standard library over time
# by reading past metrics from metrics_file, then computing today's metrics.
class KaniSTDMetricsOverTime():
    def __init__(self, metrics_file):
        self.dates = []
        self.unsafe_metrics = ['total_unsafe_fns', 'unsafe_fns_under_contract', 'verified_unsafe_fns_under_contract']
        self.safe_abstr_metrics = ['total_safe_abstractions', 'safe_abstractions_under_contract', 'verified_safe_abstractions_under_contract']
        # Generate two plots per crate: one with metrics about unsafe functions, and one with metrics about safe abstractions.
        # The keys in these dictionaries are unsafe_metrics and safe_abstr_metrics, respectively; see update_plot_metrics()
        self.unsafe_plot_data = defaultdict(list)
        self.safe_abstr_plot_data = defaultdict(list)

        self.date = datetime.today().date()
        self.metrics_file = metrics_file

        self.read_historical_data()

    # Read historical data from self.metrics_file and initialize the date range.    
    def read_historical_data(self):
        try:
            with open(self.metrics_file, 'r') as f:
                all_data = json.load(f)["results"]
                self.update_plot_metrics(all_data)
        except FileNotFoundError:
            all_data = {}
        
        self.dates = [datetime.strptime(data["date"], '%Y-%m-%d').date() for data in all_data]
        self.dates.append(self.date)
        
        print(f"Dates are {self.dates}\n")
    
    # TODO For now, we don't plot how many of the contracts have been verified, since the line overlaps with how many are under contract.
    # If we want to plot this data, we should probably generate separate plots.
    # Update the plot data with the provided data.
    def update_plot_metrics(self, all_data):
        for data in all_data:
            for metric in self.unsafe_metrics:
                if not metric.startswith("verified"):
                    self.unsafe_plot_data[metric].append(data[metric])
        
            for metric in self.safe_abstr_metrics:
                if not metric.startswith("verified"):
                    self.safe_abstr_plot_data[metric].append(data[metric])

    # Read output from kani list and std-analysis.sh, then compare their outputs to compute Kani-specific metrics
    # and write the results to {self.metrics_file}
    def compute_metrics(self, kani_list_filepath):
        # Process the `kani list` and `std-analysis.sh` data
        kani_data = KaniListSTDMetrics(kani_list_filepath)
        generic_metrics = GenericSTDMetrics()

        print("Comparing kani-list output to std-analysis.sh output and computing metrics...")

        (unsafe_fns_under_contract, verified_unsafe_fns_under_contract) = (0, 0)
        (safe_abstractions_under_contract, verified_safe_abstractions_under_contract) = (0, 0)
        (safe_fns_under_contract, verified_safe_fns_under_contract) = (0, 0)

        for (func_under_contract, has_harnesses) in kani_data.fns_under_contract:
            if func_under_contract in generic_metrics.unsafe_fns:
                unsafe_fns_under_contract += 1
                if has_harnesses:
                    verified_unsafe_fns_under_contract += 1
            elif func_under_contract in generic_metrics.safe_abstractions:
                safe_abstractions_under_contract += 1
                if has_harnesses:
                    verified_safe_abstractions_under_contract += 1
            else:
                safe_fns_under_contract += 1
                if has_harnesses:
                    verified_safe_fns_under_contract += 1

        data = {
            "date": self.date,
            "total_unsafe_fns": generic_metrics.unsafe_fns_count,
            "total_safe_abstractions": generic_metrics.safe_abstractions_count,
            "unsafe_fns_under_contract": unsafe_fns_under_contract,
            "verified_unsafe_fns_under_contract": verified_unsafe_fns_under_contract,
            "safe_abstractions_under_contract": safe_abstractions_under_contract,
            "verified_safe_abstractions_under_contract": verified_safe_abstractions_under_contract,
            "safe_fns_under_contract": safe_fns_under_contract,
            "verified_safe_fns_under_contract": verified_safe_fns_under_contract,
            "total_functions_under_contract": kani_data.total_fns_under_contract,
        }

        self.update_plot_metrics([data])

        # Update self.metrics_file so that these results are included in our historical data for next time
        with open(self.metrics_file, 'r') as f:
            content = json.load(f)
            content["results"].append(data)
        
        with open(self.metrics_file, 'w') as f:
            json.dump(content, f, indent=2, default=str)
        
        print(f"Wrote metrics data for date {self.date} to {self.metrics_file}")    

    # Make a single plot with specified data, title, and filename
    def plot_single(self, data, title, outfile):
        plt.figure(figsize=(14, 8))

        colors = ['#1f77b4', '#ff7f0e', '#2ca02c', '#d62728', '#946F7bd', '#8c564b', '#e377c2', '#7f7f7f', '#bcbd22', '#17becf']
        
        for i, (metric, values) in enumerate(data.items()):
            color = colors[i % len(colors)]
            plt.plot(self.dates, values, 'o-', color=color, label=metric, markersize=6)
            
            # Mark each point on the line with the y value
            for x, y in zip(self.dates, values):
                plt.annotate(str(y), 
                            (mdates.date2num(x), y), 
                            xytext=(0, 5), 
                            textcoords='offset points',
                            ha='center', 
                            va='bottom',
                            color=color,
                            fontweight='bold')

        plt.title(title)
        plt.xlabel("Date")
        plt.ylabel("Count")
        
        # Set x-axis to only show ticks for the dates we have
        plt.gca().xaxis.set_major_locator(FixedLocator(mdates.date2num(self.dates)))
        plt.gca().xaxis.set_major_formatter(mdates.DateFormatter('%Y-%m-%d'))
        
        plt.gcf().autofmt_xdate()
        plt.tight_layout()
        plt.legend(bbox_to_anchor=(1.05, 1), loc='upper left')
        
        plt.savefig(outfile, bbox_inches='tight', dpi=300)
        plt.close()

        print(f"PNG graph generated: {outfile}")

    def plot(self):
        self.plot_single(self.unsafe_plot_data, title="Contracts on Unsafe Functions in core", outfile="core_unsafe_std_lib_metrics.png")
        self.plot_single(self.safe_abstr_plot_data, title="Contracts on Safe Abstractions in core", outfile="core_safe_abstractions_std_lib_metrics.png")

def main():
    parser = argparse.ArgumentParser(description="Generate metrics about Kani's application to the standard library.")
    parser.add_argument('--metrics-file', 
                    type=str, 
                    default="metrics-data.json", 
                    help="Path to the JSON file containing metrics data (default: metrics-data.json)")
    parser.add_argument('--kani-list-file', 
                    type=str, 
                    default="kani-list.json", 
                    help="Path to the JSON file containing the Kani list data (default: kani-list.json)")
    args = parser.parse_args()

    metrics = KaniSTDMetricsOverTime(args.metrics_file)
    metrics.compute_metrics(args.kani_list_file)
    metrics.plot()

if __name__ == "__main__":
    main()