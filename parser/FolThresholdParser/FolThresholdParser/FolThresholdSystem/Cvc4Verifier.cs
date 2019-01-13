﻿using System;
using System.Collections.Generic;
using System.Diagnostics;
using FolThresholdParser.Utils;

namespace FolThresholdParser.FolThresholdSystem
{
    public static class Cvc4Verifier
    {
        public static IEnumerable<Specification> Verify(this IEnumerable<Specification> specs,
            FolThresholdSystem system, IProgress progress)
        {
            foreach (var specification in specs)
            {
                var result = Verify(system.AssertThresholdSmt2(specification));
                progress.Report();
                if (result) yield return specification;
            }
        }

        public static bool Verify(IEnumerable<string> smtContent)
        {
            var p = Process.Start(new ProcessStartInfo
            {
                FileName = @"c:\Users\User\ivy\cvc4-1.6-win64-opt.exe",
                Arguments = "-m --lang smt",
                UseShellExecute = false,
                RedirectStandardOutput = true,
                RedirectStandardInput = true,
                CreateNoWindow = true
            });
            if (p == null) throw new Exception("Could not start process");
            foreach (var line in smtContent)
            {
                p.StandardInput.WriteLine(line);
            }

            if(p.StandardOutput.EndOfStream) throw new Exception("Could not read result from process");
            var cvc4Result = p.StandardOutput.ReadLine() ?? "Error";

            return cvc4Result == "unsat";
        }
    }
}
