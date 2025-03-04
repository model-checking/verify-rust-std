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
import os

# Output metrics about Kani's application to the standard library by:
#   1. Postprocessing results from running `kani list`, which collects data about Kani harnesses and contracts.
#   2. Postprocessing results from std-analysis.sh, which outputs metrics about the standard library unrelated to Kani (e.g., a list of the functions in each crate).
#   3. Comparing the output of steps #1 and #2 to compare the Kani-verified portion of the standard library to the overall library,
#      e.g., what fraction of unsafe functions have Kani contracts.

# Notes:
# - This script assumes that std-analysis.sh and `kani list` have already run, since we expect to invoke this script from `run-kani.sh`.
# - The results are architecture-dependent: the standard library has functions that are only present for certain architectures, 
#   and https://github.com/model-checking/verify-rust-std/pull/122 has Kani harnesses that only run on x86-64.
# - The total functions under contract are not necessarily equal to the sum of unsafe and safe functions under contract.
#   We've added a few functions (three, as of writing) with contracts to this fork, e.g. ffi::c_str::is_null_terminated.
#   Since std-analysis.sh runs on the standard library given a toolchain (not this fork), it doesn't know about this function and therefore can't classify it as safe or unsafe.
#   But `kani list` runs on this fork, so it can still see it and add it to the total functions under contract.
# - See #TODOs for known limitations.

def str_to_bool(string: str):
    match string.strip().lower():
        case "true":
            return True
        case "false":
            return False
        case _:
            print(f"Unexpected to-be-Boolean string {string}")
            sys.exit(1)


# Process the results from Kani's std-analysis.sh script for each crate.
class GenericSTDMetrics():
    def __init__(self, results_dir, crate):
        self.results_directory = results_dir
        self.crate = crate
        self.unsafe_fns_count = 0
        self.safe_abstractions_count = 0
        self.safe_fns_count = 0
        self.unsafe_fns = []
        self.unsafe_fns_with_loop = []
        self.safe_abstractions = []
        self.safe_abstractions_with_loop = []
        self.safe_fns = [] 
        self.safe_fns_with_loop = []

        self.read_std_analysis()
        
    # Read {crate}_overall_counts.csv
    # and return the number of unsafe functions and safe abstractions
    def read_overall_counts(self):
        file_path = f"{self.results_directory}/{self.crate}_scan_overall.csv"
        with open(file_path, 'r') as f:
            csv_reader = csv.reader(f, delimiter=';')
            counts = {row[0]: int(row[1]) for row in csv_reader if len(row) >= 2}
        self.unsafe_fns_count = counts.get('unsafe_fns', 0)
        self.safe_abstractions_count = counts.get('safe_abstractions', 0)
        self.safe_fns_count = counts.get('safe_fns', 0)

    # Read {crate}_scan_functions.csv
    # and return an array of the unsafe functions and the safe abstractions
    def read_scan_functions(self):
        expected_header_start = "name;is_unsafe;has_unsafe_ops;has_unsupported_input;has_loop"
        file_path = f"{self.results_directory}/{self.crate}_scan_functions.csv"

        with open(file_path, 'r') as f:
            csv_reader = csv.reader(f, delimiter=';', quotechar='"')
            
            # The row parsing logic below assumes the column structure in expected_header_start,
            # so assert that is how the header begins before continuing
            header = next(csv_reader)
            header_str = ';'.join(header[:5])
            if not header_str.startswith(expected_header_start):
                print(f"Error: Unexpected CSV header in {file_path}")
                print(f"Expected header to start with: {expected_header_start}")
                print(f"Actual header: {header_str}")
                sys.exit(1)

            for row in csv_reader:
                if len(row) >= 5:
                    name, is_unsafe, has_unsafe_ops = row[0], row[1], row[2]
                    has_unsupported_input, has_loop = row[3], row[4]
                    # An unsafe function is a function for which is_unsafe=true
                    if str_to_bool(is_unsafe):
                        self.unsafe_fns.append(name)
                        if str_to_bool(has_loop):
                            self.unsafe_fns_with_loop.append(name)
                    else:
                        self.safe_fns.append(name)
                        if str_to_bool(has_loop):
                            self.safe_fns_with_loop.append(name)
                        # A safe abstraction is a safe function with unsafe ops
                        if str_to_bool(has_unsafe_ops):
                            self.safe_abstractions.append(name)
                            if str_to_bool(has_loop):
                                self.safe_abstractions_with_loop.append(name)

    def read_std_analysis(self):
        self.read_overall_counts()
        self.read_scan_functions()

        # Sanity checks
        if len(self.unsafe_fns) != self.unsafe_fns_count:
            print(f"Number of unsafe functions does not match {self.crate}_scan_functions.csv")
            print(f"UNSAFE_FNS_COUNT: {self.unsafe_fns_count}")
            print(f"UNSAFE_FNS length: {len(self.unsafe_fns)}")
            sys.exit(1)

        if len(self.safe_abstractions) != self.safe_abstractions_count:
            print(f"Number of safe abstractions does not match {self.crate}_scan_functions.csv")
            print(f"SAFE_ABSTRACTIONS_COUNT: {self.safe_abstractions_count}")
            print(f"SAFE_ABSTRACTIONS length: {len(self.safe_abstractions)}")
            sys.exit(1)
        
        if len(self.safe_fns) != self.safe_fns_count:
            print(f"Number of safe functions does not match {self.crate}_scan_functions.csv")
            print(f"SAFE_FNS_COUNT: {self.safe_fns_count}")
            print(f"SAFE_FNS length: {len(self.safe_fns)}")
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
    def __init__(self, metrics_file, crate):
        self.crate = crate
        self.dates = []
        self.unsafe_metrics = [
                'total_unsafe_fns',
                'total_unsafe_fns_with_loop',
                'unsafe_fns_under_contract',
                'unsafe_fns_with_loop_under_contract',
                'verified_unsafe_fns_under_contract',
                'verified_unsafe_fns_with_loop_under_contract'
                ]
        self.safe_abstr_metrics = [
                'total_safe_abstractions',
                'total_safe_abstractions_with_loop'
                'safe_abstractions_under_contract',
                'safe_abstractions_with_loop_under_contract',
                'verified_safe_abstractions_under_contract',
                'verified_safe_abstractions_with_loop_under_contract'
                ]
        self.safe_metrics = [
                'total_safe_fns',
                'total_safe_fns_with_loop',
                'safe_fns_under_contract',
                'safe_fns_with_loop_under_contract',
                'verified_safe_fns_under_contract',
                'verified_safe_fns_with_loop_under_contract'
                ]
        # The keys in these dictionaries are unsafe_metrics, safe_abstr_metrics, and safe_metrics, respectively; see update_plot_metrics()
        self.unsafe_plot_data = defaultdict(list)
        self.safe_abstr_plot_data = defaultdict(list)
        self.safe_plot_data = defaultdict(list)

        self.date = datetime.today().date()
        self.metrics_file = metrics_file

        self.read_historical_data()

    # Read historical data from self.metrics_file and initialize the date range.    
    def read_historical_data(self):
        with open(self.metrics_file, 'r') as f:
            all_data = json.load(f)["results"]
            self.update_plot_metrics(all_data)
        
        self.dates = [datetime.strptime(data["date"], '%Y-%m-%d').date() for data in all_data]
    
    # TODO For now, we don't plot how many of the contracts have been verified, since the line overlaps with how many are under contract.
    # If we want to plot this data, we should probably generate separate plots.
    # Update the plot data with the provided data.
    def update_plot_metrics(self, all_data):
        for data in all_data:
            for metric in self.unsafe_metrics:
                if not metric.startswith("verified"):
                    self.unsafe_plot_data[metric].append(data.get(metric, 0))
        
            for metric in self.safe_abstr_metrics:
                if not metric.startswith("verified"):
                    self.safe_abstr_plot_data[metric].append(data.get(metric, 0))
            
            for metric in self.safe_metrics:
                if not metric.startswith("verified"):
                    self.safe_plot_data[metric].append(data.get(metric, 0))

    # Read output from kani list and std-analysis.sh, then compare their outputs to compute Kani-specific metrics
    # and write the results to {self.metrics_file}
    def compute_metrics(self, kani_list_filepath, analysis_results_dir):
        self.dates.append(self.date)

        # Process the `kani list` and `std-analysis.sh` data
        kani_data = KaniListSTDMetrics(kani_list_filepath)
        generic_metrics = GenericSTDMetrics(analysis_results_dir, self.crate)

        print("Comparing kani-list output to std-analysis.sh output and computing metrics...")

        (unsafe_fns_under_contract, verified_unsafe_fns_under_contract) = (0, 0)
        unsafe_fns_with_loop_under_contract = 0
        verified_unsafe_fns_with_loop_under_contract = 0
        (safe_abstractions_under_contract, verified_safe_abstractions_under_contract) = (0, 0)
        safe_abstractions_with_loop_under_contract = 0
        verified_safe_abstractions_with_loop_under_contract = 0
        (safe_fns_under_contract, verified_safe_fns_under_contract) = (0, 0)
        safe_fns_with_loop_under_contract = 0
        verified_safe_fns_with_loop_under_contract = 0

        for (func_under_contract, has_harnesses) in kani_data.fns_under_contract:
            if func_under_contract in generic_metrics.unsafe_fns:
                has_loop = int(func_under_contract in
                               generic_metrics.unsafe_fns_with_loop)
                unsafe_fns_under_contract += 1
                unsafe_fns_with_loop_under_contract += has_loop
                if has_harnesses:
                    verified_unsafe_fns_under_contract += 1
                    verified_unsafe_fns_with_loop_under_contract += has_loop
            if func_under_contract in generic_metrics.safe_abstractions:
                has_loop = int(func_under_contract in
                               generic_metrics.safe_abstractions_with_loop)
                safe_abstractions_under_contract += 1
                safe_abstractions_with_loop_under_contract += has_loop
                if has_harnesses:
                    verified_safe_abstractions_under_contract += 1
                    verified_safe_abstractions_with_loop_under_contract += has_loop
            if func_under_contract in generic_metrics.safe_fns:
                has_loop = int(func_under_contract in
                               generic_metrics.safe_fns_with_loop)
                safe_fns_under_contract += 1
                safe_fns_with_loop_under_contract += has_loop
                if has_harnesses:
                    verified_safe_fns_under_contract += 1
                    verified_safe_fns_with_loop_under_contract += has_loop

        # Keep the keys here in sync with unsafe_metrics, safe_metrics, and safe_abstr_metrics
        data = {
            "date": self.date,
            "total_unsafe_fns": generic_metrics.unsafe_fns_count,
            "total_unsafe_fns_with_loop": len(generic_metrics.unsafe_fns_with_loop),
            "total_safe_abstractions": generic_metrics.safe_abstractions_count,
            "total_safe_abstractions_with_loop": len(generic_metrics.total_safe_abstractions_with_loop),
            "total_safe_fns": generic_metrics.safe_fns_count,
            "total_safe_fns_with_loop": len(generic_metrics.total_safe_fns_with_loop),
            "unsafe_fns_under_contract": unsafe_fns_under_contract,
            "unsafe_fns_with_loop_under_contract": unsafe_fns_with_loop_under_contract,
            "verified_unsafe_fns_under_contract": verified_unsafe_fns_under_contract,
            "verified_unsafe_fns_with_loop_under_contract": verified_unsafe_fns_with_loop_under_contract,
            "safe_abstractions_under_contract": safe_abstractions_under_contract,
            "safe_abstractions_with_loop_under_contract": safe_abstractions_with_loop_under_contract,
            "verified_safe_abstractions_under_contract": verified_safe_abstractions_under_contract,
            "verified_safe_abstractions_with_loop_under_contract": verified_safe_abstractions_with_loop_under_contract,
            "safe_fns_under_contract": safe_fns_under_contract,
            "safe_fns_with_loop_under_contract": safe_fns_with_loop_under_contract,
            "verified_safe_fns_under_contract": verified_safe_fns_under_contract,
            "verified_safe_fns_with_loop_under_contract": verified_safe_fns_with_loop_under_contract,
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
    def plot_single(self, data, title, filename, plot_dir):
        plt.figure(figsize=(14, 8))

        colors = [
                '#1f77b4', #total_unsafe_fns
                '#941fb4', #total_unsafe_fns_with_loop
                '#ff7f0e', #total_safe_abstractions
                '#abff0e', #total_safe_abstractions_with_loop
                '#2ca02c', #total_safe_fns
                '#a02c8d', #total_safe_fns_with_loop
                '#d62728', #unsafe_fns_under_contract
                '#27d6aa', #unsafe_fns_with_loop_under_contract
                '#9467bd', #verified_unsafe_fns_under_contract
                '#67acbd', #verified_unsafe_fns_with_loop_under_contract
                '#8c564b', #safe_abstractions_under_contract
                '#8c814b', #safe_abstractions_with_loop_under_contract
                '#e377c2', #verified_safe_abstractions_under_contract
                '#a277e3', #verified_safe_abstractions_with_loop_under_contract
                '#7f7f7f', #safe_fns_under_contract
                '#9e6767', #safe_fns_with_loop_under_contract
                '#bcbd22', #verified_safe_fns_under_contract
                '#49bd22', #verified_safe_fns_with_loop_under_contract
                '#17becf' #total_functions_under_contract
                ]
        
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
        
        outfile = os.path.join(plot_dir, filename)

        plt.savefig(outfile, bbox_inches='tight', dpi=300)
        plt.close()

        print(f"PNG graph generated: {outfile}")

    def plot(self, plot_dir):
        self.plot_single(
            self.unsafe_plot_data,
            title=f"Contracts on Unsafe Functions in {self.crate}",
            filename=f"{self.crate}_unsafe_metrics.png",
            plot_dir=plot_dir)
        self.plot_single(
            self.safe_abstr_plot_data,
            title=f"Contracts on Safe Abstractions in {self.crate}",
            filename=f"{self.crate}_safe_abstractions_metrics.png",
            plot_dir=plot_dir)
        self.plot_single(
            self.safe_plot_data,
            title=f"Contracts on Safe Functions in {self.crate}",
            filename=f"{self.crate}_safe_metrics.png",
            plot_dir=plot_dir)

def main():
    parser = argparse.ArgumentParser(description="Generate metrics about Kani's application to the standard library.")
    parser.add_argument('--crate',
                    type=str,
                    required=True,
                    help="Name of standard library crate to produce metrics for")
    parser.add_argument('--metrics-file', 
                    type=str, 
                    required=True,
                    help="Path to the JSON file containing metrics data")
    parser.add_argument('--kani-list-file', 
                    type=str, 
                    default="kani-list.json", 
                    help="Path to the JSON file containing the Kani list data (default: kani-list.json)")
    # The default is /tmp/std_lib_analysis/results because, as of writing, that's always where std-analysis.sh outputs its results.
    parser.add_argument('--analysis-results-dir', 
                    type=str, 
                    default="/tmp/std_lib_analysis/results", 
                    help="Path to the folder file containing the std-analysis.sh results (default: /tmp/std_lib_analysis/results)")
    parser.add_argument('--plot-only', 
                    action='store_true',
                    help="Instead of computing the metrics, just read existing metrics from --metrics-file and plot the results.")
    parser.add_argument('--plot-dir',
                        default=".",
                        help="Path to the folder where the plots should be saved (default: current directory). Only used if --plot-only is provided.")
    
    args = parser.parse_args()

    metrics = KaniSTDMetricsOverTime(args.metrics_file, args.crate)

    if args.plot_only:
        metrics.plot(args.plot_dir)
    else:
        metrics.compute_metrics(args.kani_list_file, args.analysis_results_dir)

if __name__ == "__main__":
    main()
