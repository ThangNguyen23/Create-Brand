import unittest

import create_brand as brand


class GoogleDriveUrlTests(unittest.TestCase):
    def test_splits_and_deduplicates_adjacent_drive_folder_urls(self):
        url = "https://drive.google.com/drive/folders/1aIip8aISU1VLHR4nVJbesGIIYyZwZDWH"
        urls = brand._extract_urls(url + url)

        self.assertEqual(urls, [url])
        self.assertEqual(
            brand._extract_gdrive_folder_id(urls[0]),
            "1aIip8aISU1VLHR4nVJbesGIIYyZwZDWH",
        )

    def test_does_not_accept_concatenated_url_as_a_drive_id(self):
        malformed_url = (
            "https://drive.google.com/drive/folders/"
            "1aIip8aISU1VLHR4nVJbesGIIYyZwZDWHhttps://drive.google.com/drive/"
        )
        self.assertIsNone(brand._extract_gdrive_folder_id(malformed_url))


if __name__ == "__main__":
    unittest.main()
