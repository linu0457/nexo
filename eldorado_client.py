"""Minimal Eldorado.gg Seller API client.

From the dashboard:
- Base URL:  https://www.eldorado.gg (without www, POST is redirected to GET -> 405)
- Token:     POST /api/authentication/seller/token  {"clientId", "clientSecret"}
             -> {"accessToken", "expiresIn": 900, "tokenType": "Bearer"}
- Calls:     Authorization: Bearer <accessToken>

Other endpoints come from Eldorado's swagger spec:
https://www.eldorado.gg/swagger/seller/index.html
"""
import os
import time

import requests
from dotenv import load_dotenv

load_dotenv()

BASE_URL = "https://www.eldorado.gg"
TRANSIENT = {500, 502, 503, 504, 520, 521, 522, 523, 524}


class EldoradoClient:
    def __init__(self, client_id=None, client_secret=None, timeout=15):
        self.client_id = client_id or os.environ["ELDORADO_CLIENT_ID"]
        self.client_secret = client_secret or os.environ["ELDORADO_CLIENT_SECRET"]
        self.timeout = timeout
        self._token = None
        self._expires_at = 0.0

    def _refresh_token(self):
        r = requests.post(
            f"{BASE_URL}/api/authentication/seller/token",
            json={"clientId": self.client_id, "clientSecret": self.client_secret},
            timeout=self.timeout,
        )
        r.raise_for_status()
        data = r.json()
        self._token = data["accessToken"]
        # Renew 60 seconds before expiry (tokens last 15 minutes)
        self._expires_at = time.time() + data.get("expiresIn", 900) - 60

    def _headers(self):
        if not self._token or time.time() >= self._expires_at:
            self._refresh_token()
        return {
            "Authorization": f"Bearer {self._token}",
            "Content-Type": "application/json",
        }

    def request(self, method, path, **kwargs):
        """General call. Renews the token and retries once on 401."""
        kwargs.setdefault("timeout", self.timeout)
        url = f"{BASE_URL}{path}"
        # Eldorado sits behind Cloudflare, which now and then answers 520-524 / 502-504 for a second. That is nothing
        # on your side: try again a couple of times before reporting an error (reads only, a change is never repeated).
        tries = 3 if method.upper() == "GET" else 1
        for n in range(tries):
            try:
                r = requests.request(method, url, headers=self._headers(), **kwargs)
                if r.status_code == 401:
                    self._token = None
                    r = requests.request(method, url, headers=self._headers(), **kwargs)
                if r.status_code in TRANSIENT and n < tries - 1:
                    time.sleep(1.5 * (n + 1))
                    continue
                break
            except (requests.ConnectionError, requests.Timeout):
                if n >= tries - 1:
                    raise
                time.sleep(1.5 * (n + 1))
        r.raise_for_status()
        return r.json() if r.content else None

    # --- Endpoints from Eldorado's swagger spec (seller API) ---

    def seller_api_eligibility(self):
        return self.request("GET", "/api/v1/orders/me/seller-api-eligibility")

    def list_seller_orders(self, order_state="Paid", page_size=50):
        """Your sales. order_state: Paid (needs delivery), Disputed, Delivered,
        Received, Completed, Canceled, PendingReview. First page only (max 50)."""
        params = {
            "displayFilter": "DisplaySellingOrders",
            "orderState": order_state,
            "pageSize": page_size,
        }
        return self.request("GET", "/api/v1/orders/me/seller/orders", params=params)

    def mark_delivered(self, order_id):
        """CHANGES A REAL ORDER. Only call when the item has actually been delivered."""
        return self.request("PUT", f"/api/v1/orders/me/{order_id}/deliver")


if __name__ == "__main__":
    # Only tests login (makes no changes to your account)
    client = EldoradoClient()
    client._refresh_token()
    print("Login OK. Token expires in about", int(client._expires_at - time.time()) + 60, "seconds.")
