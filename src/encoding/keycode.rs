use std::ops::Bound;

// 示例
// 假设前缀是 [0x01, 0x02, 0x03]：

// 起始边界是 Bound::Included(vec![0x01, 0x02, 0x03])。
// 结束边界是 Bound::Excluded(vec![0x01, 0x02, 0x04])。
// 假设前缀是 [0xff, 0xff, 0xff]：

// 起始边界是 Bound::Included(vec![0xff, 0xff, 0xff])。
// 结束边界是 Bound::Unbounded。
pub fn prefix_range(prefix: &[u8]) -> (Bound<Vec<u8>>, Bound<Vec<u8>>) {
    let start = Bound::Included(prefix.to_vec());
    let end = match prefix.iter().rposition(|b| *b != 0xff) {
        Some(i) => Bound::Excluded(
            prefix.iter().take(i).copied().chain(std::iter::once(prefix[i] + 1)).collect(),
        ),
        None => Bound::Unbounded,
    };
    (start, end)
}

