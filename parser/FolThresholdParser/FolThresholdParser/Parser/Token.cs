using System;
using System.Text.RegularExpressions;

namespace FolThresholdParser.Parser
{
    public enum SyntaxGeneralType
    {
        None,
        MathOperators,
        SetOperators,
        ComparisonOperators,
        VariableName,
        LiteralNumber,
        WhiteSpaceLiteral,
        Keyword,
        Parenthesis
    }

    public enum SyntaxKind
    {
        None = 0,

        // math operators
        PlusOperationToken,
        MinusOperationToken,
        DivOperationToken,

        // set operators
        AndOperationToken,
        OrOperationToken,
        ComplementOperationToken,

        // comparison tokens
        EqualToken,
        InEqualToken,
        GreaterThanToken,
        GeqThanToken,
        LessThanToken,
        LeqThanToken,

        VariableNameToken,
        LiteralNumberToken,
        WhitespaceToken,

        DotToken,
        CommaToken,
        ColonToken,

        // identifier keyword
        ConstantKeyword,
        NaturalKeyword,
        QuorumKeyword,
        AxiomKeyword,
        ConjectureKeyword,
        NonEmptyKeyword,
        SetKeyword,

        NotKeyword,
        AndKeyword,
        OrKeyword,

        ForallSetKeyword,
        ExistsSetKeyword,
        
        OpenParenthesisToken,
        CloseParenthesisToken        
    }


    public class Token
    {
        public int Start { get; }
        public int Length { get; }
        public int Line;
        public SyntaxKind Type { get; }
        public SyntaxGeneralType GeneralType => GetSyntaxGlobalType(Type);
        public string Code;

        public Token(int start, int length, SyntaxKind type, string code, int line)
        {
            Start = start;
            Length = length;
            Type = type;
            Code = code;
            Line = line;
        }

        public override string ToString() => $"{Code} <{Type}> start: {Start} length: {Length} value: {Evaluate}";
        public string Evaluate => $"'{Regex.Escape(Code.Substring(Start, Length))}'";
        public string Value => Code.Substring(Start, Length); //type == SyntaxKind.EOLToken ? Environment.NewLine :

        public static SyntaxGeneralType GetSyntaxGlobalType(SyntaxKind kind)
        {
            switch (kind)
            {
                case SyntaxKind.None:
                    return SyntaxGeneralType.None;
                case SyntaxKind.PlusOperationToken:
                case SyntaxKind.MinusOperationToken:
                case SyntaxKind.DivOperationToken:
                    return SyntaxGeneralType.MathOperators;
                case SyntaxKind.AndOperationToken:
                case SyntaxKind.OrOperationToken:
                case SyntaxKind.ComplementOperationToken:
                    return SyntaxGeneralType.SetOperators;
                case SyntaxKind.EqualToken:
                case SyntaxKind.InEqualToken:
                case SyntaxKind.GreaterThanToken:
                case SyntaxKind.GeqThanToken:
                case SyntaxKind.LessThanToken:
                case SyntaxKind.LeqThanToken:
                    return SyntaxGeneralType.ComparisonOperators;
                case SyntaxKind.VariableNameToken:
                    return SyntaxGeneralType.VariableName;
                case SyntaxKind.LiteralNumberToken:
                    return SyntaxGeneralType.LiteralNumber;
                case SyntaxKind.WhitespaceToken:
                    return SyntaxGeneralType.WhiteSpaceLiteral;
                case SyntaxKind.ConstantKeyword:
                case SyntaxKind.NaturalKeyword:
                case SyntaxKind.QuorumKeyword:
                case SyntaxKind.AxiomKeyword:
                case SyntaxKind.ConjectureKeyword:
                case SyntaxKind.NonEmptyKeyword:
                case SyntaxKind.SetKeyword:
                case SyntaxKind.NotKeyword:
                case SyntaxKind.AndKeyword:
                case SyntaxKind.OrKeyword:
                    return SyntaxGeneralType.Keyword;
                case SyntaxKind.OpenParenthesisToken:
                case SyntaxKind.CloseParenthesisToken:
                    return SyntaxGeneralType.Parenthesis;
                default:
                    throw new ArgumentOutOfRangeException(nameof(kind), kind, null);
            }
        }
    }
}