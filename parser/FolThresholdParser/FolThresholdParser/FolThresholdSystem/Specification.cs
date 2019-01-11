using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using FolThresholdParser.FolSyntax;
using FolThresholdParser.Parser;
using FolThresholdParser.Utils;

namespace FolThresholdParser.FolThresholdSystem
{
    public abstract class Specification
    {
        public readonly bool Conjecture;

        protected Specification(bool conjecture)
        {
            Conjecture = conjecture;
        }

        public static Specification Parse(ArrayView<Token> tokens)
        {
            bool conjecture = tokens[0].Type == SyntaxKind.ConjectureKeyword;

            switch (tokens[1].Type)
            {
                case SyntaxKind.NaturalKeyword:
                    return new NaturalSpecification(conjecture, tokens);
                //case SyntaxKind.NonEmptyKeyword:
                    //return NonEmptySetFormula.ParseInternal(conjecture, tokens.Skip(2));
                case SyntaxKind.SetKeyword:
                    return new SetSpecification(conjecture, tokens);
                default:
                    return null;
            }
        }
    }

    public class NaturalSpecification : Specification
    {
        public readonly Formula Formula;

        public NaturalSpecification(bool conjecture, ArrayView<Token> tokens) : base(conjecture)
        {
            Formula = NaturalFormula.Parse(tokens.Skip(2));
        }
    }

    public class SetSpecification : Specification
    {
        public readonly Formula Formula;

        public SetSpecification(bool conjecture, ArrayView<Token> tokens) : base(conjecture)
        {
            Formula = SetFormula.Parse(tokens.Skip(2));
        }
    }
}
