using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;

namespace FolThresholdParser.Utils
{
    public struct ArrayView<T> : IEnumerable<T>
    {
        private readonly T[] _array;
        private readonly int _offset;
        private readonly int _length;

        private ArrayView(T[] array, int offset, int length)
        {
            _array = array;
            _offset = offset;
            _length = length;
        }

        public static implicit operator ArrayView<T>(T[] array)
        {
            return new ArrayView<T>(array, 0, array.Length);
        }

        public T this[int index]
        {
            get
            {
                index += _offset;
                CheckInbound(index);
                return _array[index];
            }
            set
            {
                index += _offset;
                CheckInbound(index);
                _array[index] = value;
            }
        }

        public int Length => _length;

        private void CheckInbound(int index)
        {
            if (index < 0) throw new IndexOutOfRangeException();
            if (index < _offset) throw new IndexOutOfRangeException();
            if (index >= _offset + _length) throw new IndexOutOfRangeException();
            if (index >= _array.Length) throw new IndexOutOfRangeException();
        }

        private ArrayView<T> CreateView(int newOffset, int newLength)
        {
            CheckInbound(newOffset);
            if (newLength > 0) CheckInbound(newOffset + newLength - 1);

            return new ArrayView<T>(_array, newOffset, newLength);
        }

        public ArrayView<T> Skip(int items)
        {
            return CreateView(_offset + items, _length - items);
        }

        public ArrayView<T> Take(int items)
        {
            return CreateView(_offset, items);
        }

        private IEnumerable<T> AsEnumerable()
        {
            return _array.Skip(_offset).Take(_length);
        }

        public IEnumerator<T> GetEnumerator()
        {
            return AsEnumerable().GetEnumerator();
        }

        IEnumerator IEnumerable.GetEnumerator()
        {
            return AsEnumerable().GetEnumerator();
        }
    }
}
