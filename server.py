import os
import time
import uuid
import json
import hmac
import base64
import hashlib
import datetime
import logging
import ipaddress
import secrets
import re
import threading
from typing import Dict, List, Optional, Tuple, Any, Union
from collections import defaultdict

# Enhanced libraries
from fastapi import FastAPI, Depends, HTTPException, Request, status, BackgroundTasks
from fastapi.security import APIKeyHeader, OAuth2PasswordBearer, OAuth2PasswordRequestForm
from fastapi.middleware.cors import CORSMiddleware
from fastapi.middleware.gzip import GZipMiddleware
from pydantic import BaseModel, EmailStr, Field, validator, constr
from sqlalchemy import create_engine, Column, String, Boolean, DateTime, Integer, ForeignKey, Text, func, Index, event
from sqlalchemy.orm import declarative_base
from sqlalchemy.orm import sessionmaker, Session, relationship, scoped_session
from sqlalchemy.sql import func
from sqlalchemy.dialects.postgresql import JSON, JSONB
from sqlalchemy.pool import QueuePool
from cryptography.hazmat.primitives.asymmetric import ec, rsa, padding
from cryptography.hazmat.primitives import hashes, serialization, constant_time
from cryptography.hazmat.primitives.serialization import load_pem_private_key
from cryptography.hazmat.backends import default_backend
from cryptography.fernet import Fernet, MultiFernet
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from jose import jwt, JWTError
from passlib.context import CryptContext
import pyotp
import qrcode
from io import BytesIO
import base64
from starlette.requests import Request
from starlette.responses import JSONResponse, Response
from starlette.middleware.base import BaseHTTPMiddleware
from prometheus_client import Counter, Histogram, start_http_server
import redis
import pickle
import zlib
from datetime import timedelta
from prometheus_client import generate_latest
from dotenv import load_dotenv


# Create FastAPI app
app = FastAPI(
    title="License Management System API",
    description="A secure API for license management with advanced security features",
    version="1.0.0"
)


# Configure structured logging
class JSONFormatter(logging.Formatter):
    def format(self, record):
        log_record = {
            "timestamp": datetime.datetime.now(datetime.UTC)
.isoformat(),
            "level": record.levelname,
            "message": record.getMessage(),
            "module": record.module,
            "function": record.funcName,
            "line": record.lineno
        }

        # Add exception info if present
        if record.exc_info:
            log_record["exception"] = {
                "type": record.exc_info[0].__name__,
                "message": str(record.exc_info[1]),
            }

        # Add extra fields from record
        for key, value in record.__dict__.items():
            if key not in ["args", "asctime", "created", "exc_info", "exc_text",
                           "filename", "funcName", "id", "levelname", "levelno",
                           "lineno", "module", "msecs", "message", "msg",
                           "name", "pathname", "process", "processName",
                           "relativeCreated", "stack_info", "thread", "threadName"]:
                log_record[key] = value

        return json.dumps(log_record)


# Configure logging with JSON formatter
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler("license_server.log"),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger("license_server")
for handler in logger.handlers:
    handler.setFormatter(JSONFormatter())

# Initialize database - Switching to PostgreSQL for production
DATABASE_URL = os.getenv("DATABASE_URL", "postgresql://postgres:MniTHbo7162005@localhost:5432/postgres")
engine = create_engine(
    DATABASE_URL,
    pool_size=50,  # MAXED OUT FOR SPEED
    max_overflow=20,  # EXTRA HEADROOM
    pool_timeout=10,  # NO BLOCKING
    pool_recycle=1800,  # KICKS IDLE CONNECTIONS
    echo=False
)

SessionLocal = scoped_session(sessionmaker(autocommit=False, autoflush=False, bind=engine))
Base = declarative_base()

# Initialize Redis for caching and rate limiting
REDIS_URL = os.getenv("REDIS_URL", "redis://localhost:6379/0")
redis_client = redis.Redis(host='localhost', port=6379, db=0)

# Constants
KEY_VALID_DAYS = {"basic": 30, "premium": 365}
ADMIN_API_KEY = os.getenv("ADMIN_API_KEY", "admin_secure_key_change_in_production")
MAX_FAILED_VALIDATIONS = 5
ANOMALY_THRESHOLD = 3
TOKEN_EXPIRY_HOURS = 24
ACCESS_TOKEN_EXPIRE_MINUTES = 30
REFRESH_TOKEN_EXPIRE_DAYS = 7
SECRET_KEY = os.getenv("JWT_SECRET_KEY", secrets.token_hex(32))
ALGORITHM = "HS256"

# Rate limiting settings
RATE_LIMIT_WINDOW = 60  # 1 minute window
RATE_LIMIT_MAX_REQUESTS = {
    "/api/license/validate": 10,  # 10 requests per minute
    "/api/tweak/configurations": 20,  # 20 requests per minute
    "default": 100  # Default limit for other endpoints
}

# Metrics
HTTP_REQUESTS = Counter('http_requests_total', 'Total HTTP Requests', ['method', 'endpoint', 'status'])
REQUEST_LATENCY = Histogram('http_request_duration_seconds', 'HTTP Request Latency', ['method', 'endpoint'])


# Setup Key Management Service (KMS)
class KeyManagementService:
    """A simplified KMS implementation for key management."""

    def __init__(self, storage_path="./keys"):
        self.storage_path = storage_path
        os.makedirs(storage_path, exist_ok=True)

        # Key rotation settings
        self.rotation_interval = {
            "private_key": 90,  # days
            "fernet_key": 30,  # days
            "jwt_secret": 14  # days
        }

        # Initialize or load keys
        self.load_or_initialize_keys()

        # Schedule key rotation
        self.schedule_key_rotation()

    def load_or_initialize_keys(self):
        """Initialize or load cryptographic keys."""
        # Load or generate ECC private key for license signing
        self.private_key = self._load_or_initialize_private_key()

        # Load or generate Fernet keys for symmetric encryption
        self.fernet_keys = self._load_or_initialize_fernet_keys()
        self.fernet = MultiFernet([Fernet(key) for key in self.fernet_keys])

        # Load or generate JWT secrets
        self.jwt_secrets = self._load_or_initialize_jwt_secrets()
        self.current_jwt_secret = self.jwt_secrets[0] if self.jwt_secrets else None

    def _load_or_initialize_private_key(self):
        """Load existing or create new ECC private key."""
        private_key_path = os.path.join(self.storage_path, "private_key.pem")
        public_key_path = os.path.join(self.storage_path, "public_key.pem")

        # Check if the key exists
        if os.path.exists(private_key_path):
            # Check if rotation is needed
            if self._is_rotation_needed(private_key_path, "private_key"):
                # Backup old key
                self._backup_key(private_key_path)
                self._backup_key(public_key_path)

                # Generate new key
                return self._generate_private_key(private_key_path, public_key_path)
            else:
                # Load existing key
                with open(private_key_path, "rb") as f:
                    return load_pem_private_key(f.read(), password=None, backend=default_backend())
        else:
            # Generate new key
            return self._generate_private_key(private_key_path, public_key_path)

    def _generate_private_key(self, private_key_path, public_key_path):
        """Generate a new ECC private key and save it."""
        private_key = ec.generate_private_key(ec.SECP256R1(), default_backend())

        # Save private key
        with open(private_key_path, "wb") as f:
            f.write(private_key.private_bytes(
                encoding=serialization.Encoding.PEM,
                format=serialization.PrivateFormat.PKCS8,
                encryption_algorithm=serialization.NoEncryption()
            ))

        # Save public key
        with open(public_key_path, "wb") as f:
            f.write(private_key.public_key().public_bytes(
                encoding=serialization.Encoding.PEM,
                format=serialization.PublicFormat.SubjectPublicKeyInfo
            ))

        # Update timestamp
        self._update_timestamp(private_key_path)

        return private_key

    def _load_or_initialize_fernet_keys(self):
        """Load existing or create new Fernet keys."""
        fernet_keys_path = os.path.join(self.storage_path, "fernet_keys.json")

        # Check if keys exist
        if os.path.exists(fernet_keys_path):
            # Check if rotation is needed
            if self._is_rotation_needed(fernet_keys_path, "fernet_key"):
                # Load existing keys
                with open(fernet_keys_path, "r") as f:
                    keys = json.load(f)

                # Generate new key and prepend to list
                new_key = Fernet.generate_key()
                keys.insert(0, new_key.decode())

                # Keep only the latest 3 keys
                keys = keys[:3]

                # Save updated keys
                with open(fernet_keys_path, "w") as f:
                    json.dump(keys, f)

                # Update timestamp
                self._update_timestamp(fernet_keys_path)

                return [key.encode() for key in keys]
            else:
                # Load existing keys
                with open(fernet_keys_path, "r") as f:
                    keys = json.load(f)
                return [key.encode() for key in keys]
        else:
            # Generate new key
            new_key = Fernet.generate_key()
            keys = [new_key.decode()]

            # Save new key
            with open(fernet_keys_path, "w") as f:
                json.dump(keys, f)

            # Update timestamp
            self._update_timestamp(fernet_keys_path)

            return [new_key]

    def _load_or_initialize_jwt_secrets(self):
        """Load existing or create new JWT secrets."""
        jwt_secrets_path = os.path.join(self.storage_path, "jwt_secrets.json")

        # Check if secrets exist
        if os.path.exists(jwt_secrets_path):
            # Check if rotation is needed
            if self._is_rotation_needed(jwt_secrets_path, "jwt_secret"):
                # Load existing secrets
                with open(jwt_secrets_path, "r") as f:
                    secrets_list = json.load(f)

                # Generate new secret and prepend to list
                new_secret = secrets.token_hex(32)
                secrets_list.insert(0, new_secret)

                # Keep only the latest 3 secrets
                secrets_list = secrets_list[:3]

                # Save updated secrets
                with open(jwt_secrets_path, "w") as f:
                    json.dump(secrets_list, f)

                # Update timestamp
                self._update_timestamp(jwt_secrets_path)

                return secrets_list
            else:
                # Load existing secrets
                with open(jwt_secrets_path, "r") as f:
                    return json.load(f)
        else:
            # Generate new secret
            new_secret = secrets.token_hex(32)
            secrets_list = [new_secret]

            # Save new secret
            with open(jwt_secrets_path, "w") as f:
                json.dump(secrets_list, f)

            # Update timestamp
            self._update_timestamp(jwt_secrets_path)

            return secrets_list

    def _is_rotation_needed(self, file_path, key_type):
        """Check if a key needs to be rotated based on its age."""
        if not os.path.exists(file_path):
            return True

        timestamp_path = f"{file_path}.timestamp"
        if not os.path.exists(timestamp_path):
            return True

        with open(timestamp_path, "r") as f:
            timestamp_str = f.read().strip()

        try:
            timestamp = datetime.datetime.fromisoformat(timestamp_str)
            if timestamp.tzinfo is None:  # If timestamp is naive, make it aware
                timestamp = timestamp.replace(tzinfo=datetime.UTC)

            age_days = (datetime.datetime.now(datetime.UTC) - timestamp).days
            return age_days >= self.rotation_interval[key_type]
        except ValueError:
            return True

    def _update_timestamp(self, file_path):
        """Update the timestamp file for a key."""
        timestamp_path = f"{file_path}.timestamp"
        with open(timestamp_path, "w") as f:
            f.write(datetime.datetime.now(datetime.UTC).isoformat())

    def _backup_key(self, file_path):
        """Create a backup of a key file."""
        if os.path.exists(file_path):
            backup_dir = os.path.join(self.storage_path, "backup")
            os.makedirs(backup_dir, exist_ok=True)

            filename = os.path.basename(file_path)
            timestamp = datetime.datetime.now(datetime.UTC).strftime("%Y%m%d%H%M%S")
            backup_path = os.path.join(backup_dir, f"{filename}.{timestamp}")

            with open(file_path, "rb") as src, open(backup_path, "wb") as dst:
                dst.write(src.read())

    def schedule_key_rotation(self):
        """Schedule periodic key rotation."""

        # This would be better with a proper scheduler like APScheduler,
        # but we'll use a simple thread for demonstration
        def rotation_job():
            while True:
                try:
                    # Check private key
                    private_key_path = os.path.join(self.storage_path, "private_key.pem")
                    if self._is_rotation_needed(private_key_path, "private_key"):
                        logger.info("Rotating private key")
                        self._backup_key(private_key_path)
                        self._backup_key(os.path.join(self.storage_path, "public_key.pem"))
                        self.private_key = self._generate_private_key(
                            private_key_path,
                            os.path.join(self.storage_path, "public_key.pem")
                        )

                    # Check Fernet keys
                    fernet_keys_path = os.path.join(self.storage_path, "fernet_keys.json")
                    if self._is_rotation_needed(fernet_keys_path, "fernet_key"):
                        logger.info("Rotating Fernet keys")
                        self.fernet_keys = self._load_or_initialize_fernet_keys()
                        self.fernet = MultiFernet([Fernet(key) for key in self.fernet_keys])

                    # Check JWT secrets
                    jwt_secrets_path = os.path.join(self.storage_path, "jwt_secrets.json")
                    if self._is_rotation_needed(jwt_secrets_path, "jwt_secret"):
                        logger.info("Rotating JWT secrets")
                        self.jwt_secrets = self._load_or_initialize_jwt_secrets()
                        self.current_jwt_secret = self.jwt_secrets[0] if self.jwt_secrets else None

                except Exception as e:
                    logger.error(f"Error in key rotation: {str(e)}")

                # Sleep for 1 day
                time.sleep(86400)

        # Start rotation thread
        rotation_thread = threading.Thread(target=rotation_job, daemon=True)
        rotation_thread.start()

    def encrypt(self, data):
        """Encrypt data using Fernet."""
        if isinstance(data, dict) or isinstance(data, list):
            data = json.dumps(data)
        if isinstance(data, str):
            data = data.encode()
        return self.fernet.encrypt(data)

    def decrypt(self, encrypted_data):
        """Decrypt data using Fernet."""
        decrypted = self.fernet.decrypt(encrypted_data)
        try:
            return json.loads(decrypted)
        except json.JSONDecodeError:
            return decrypted

    def sign_license(self, payload):
        """Sign a license payload with ECC private key."""
        if isinstance(payload, dict):
            payload = json.dumps(payload)
        if isinstance(payload, str):
            payload = payload.encode()

        signature = self.private_key.sign(
            payload,
            ec.ECDSA(hashes.SHA256())
        )

        return base64.b64encode(signature).decode()

    def verify_license(self, payload, signature):
        """Verify a license signature."""
        if isinstance(payload, dict):
            payload = json.dumps(payload)
        if isinstance(payload, str):
            payload = payload.encode()

        signature_bytes = base64.b64decode(signature)

        try:
            self.private_key.public_key().verify(
                signature_bytes,
                payload,
                ec.ECDSA(hashes.SHA256())
            )
            return True
        except Exception:
            return False

    def create_jwt(self, data, expires_delta=None):
        """Create a JWT token."""
        to_encode = data.copy()

        if expires_delta:
            expire = datetime.datetime.now(datetime.UTC) + expires_delta
        else:
            expire = datetime.datetime.now(datetime.UTC) + datetime.timedelta(minutes=15)

        to_encode.update({"exp": expire})

        # Use the most recent secret
        encoded_jwt = jwt.encode(to_encode, self.current_jwt_secret, algorithm=ALGORITHM)
        return encoded_jwt

    def verify_jwt(self, token):
        """Verify a JWT token against all recent secrets."""
        for secret in self.jwt_secrets:
            try:
                payload = jwt.decode(token, secret, algorithms=[ALGORITHM])
                return payload
            except JWTError:
                continue

        raise ValueError("Invalid token")


# Initialize KMS
kms = KeyManagementService()

# Password context for hashing
pwd_context = CryptContext(schemes=["bcrypt"], deprecated="auto")


# Create Merkle Tree for tamper-evident logs
class MerkleNode:
    def __init__(self, data=None, left=None, right=None):
        self.data = data
        self.left = left
        self.right = right
        self.hash = self._calculate_hash()

    def _calculate_hash(self):
        if self.data:
            return hashlib.sha256(self.data.encode()).hexdigest()
        elif self.left and self.right:
            combined = self.left.hash + self.right.hash
            return hashlib.sha256(combined.encode()).hexdigest()
        return None


class MerkleTree:
    def __init__(self):
        self.leaves = []
        self.root = None
        self.persistence_path = "./merkle_tree_data.json"
        self.load_tree()

    def add_leaf(self, data):
        if isinstance(data, dict):
            data = json.dumps(data)
        leaf = MerkleNode(data=data)
        self.leaves.append(leaf)
        self._rebuild_tree()
        self.save_tree()
        return leaf.hash

    def _rebuild_tree(self):
        if not self.leaves:
            self.root = None
            return

        nodes = self.leaves.copy()
        while len(nodes) > 1:
            new_level = []
            for i in range(0, len(nodes), 2):
                if i + 1 < len(nodes):
                    new_node = MerkleNode(left=nodes[i], right=nodes[i + 1])
                else:
                    new_node = MerkleNode(left=nodes[i], right=nodes[i])
                new_level.append(new_node)
            nodes = new_level

        self.root = nodes[0]

    def get_root_hash(self):
        return self.root.hash if self.root else None

    def save_tree(self):
        """Save Merkle tree data to disk for persistence."""
        data = {
            "leaves": [leaf.data for leaf in self.leaves],
            "root_hash": self.get_root_hash()
        }

        # Save to file
        with open(self.persistence_path, "w") as f:
            json.dump(data, f)

        # Also save to an append-only log for additional security
        with open("./merkle_tree_log.txt", "a") as f:
            entry = {
                "timestamp": datetime.datetime.now(datetime.UTC).isoformat(),
                "root_hash": self.get_root_hash(),
                "leaf_count": len(self.leaves)
            }
            f.write(json.dumps(entry) + "\n")

    def load_tree(self):
        """Load Merkle tree data from disk."""
        if os.path.exists(self.persistence_path):
            try:
                with open(self.persistence_path, "r") as f:
                    data = json.load(f)

                # Recreate leaves
                self.leaves = [MerkleNode(data=leaf_data) for leaf_data in data["leaves"]]

                # Rebuild tree
                self._rebuild_tree()

                logger.info(f"Loaded Merkle tree with {len(self.leaves)} leaves")
            except Exception as e:
                logger.error(f"Error loading Merkle tree: {str(e)}")
                self.leaves = []
                self.root = None
        else:
            self.leaves = []
            self.root = None


# Initialize Merkle tree for license logs
license_log_tree = MerkleTree()


# Enhanced database models with indices and constraints
class User(Base):
    __tablename__ = "users"

    id = Column(String(36), primary_key=True, index=True)
    email = Column(String(255), unique=True, index=True, nullable=False)
    discord_id = Column(String(255), unique=True, index=True)
    created_at = Column(DateTime, server_default=func.now(), nullable=False)
    is_banned = Column(Boolean, default=False, nullable=False)
    licenses = relationship("License", back_populates="user", cascade="all, delete-orphan")
    mfa_secret = Column(String(255), nullable=True)
    mfa_enabled = Column(Boolean, default=False)

    # Add index for faster banned user lookup
    __table_args__ = (
        Index('idx_user_banned', 'is_banned'),
    )


class AdminUser(Base):
    __tablename__ = "admin_users"

    id = Column(String(36), primary_key=True, index=True)
    username = Column(String(255), unique=True, index=True, nullable=False)
    email = Column(String(255), unique=True, index=True, nullable=False)
    hashed_password = Column(String(255), nullable=False)
    is_active = Column(Boolean, default=True, nullable=False)
    is_superuser = Column(Boolean, default=False, nullable=False)
    created_at = Column(DateTime, server_default=func.now(), nullable=False)
    last_login = Column(DateTime, nullable=True)
    mfa_secret = Column(String(255), nullable=True)
    mfa_enabled = Column(Boolean, default=False)

    def verify_password(self, password):
        return pwd_context.verify(password, self.hashed_password)


class License(Base):
    __tablename__ = "licenses"

    id = Column(String(36), primary_key=True, index=True)
    user_id = Column(String(36), ForeignKey("users.id"), nullable=False)
    license_type = Column(String(50), nullable=False)
    created_at = Column(DateTime, server_default=func.now(), nullable=False)
    expires_at = Column(DateTime, nullable=False)
    is_active = Column(Boolean, default=True, nullable=False)
    hwid = Column(String(255), nullable=True)
    user = relationship("User", back_populates="licenses")
    activations = relationship("Activation", back_populates="license", cascade="all, delete-orphan")
    modifications = relationship("LicenseModification", back_populates="license", cascade="all, delete-orphan")

    # Add indices for faster querying
    __table_args__ = (
        Index('idx_license_type', 'license_type'),
        Index('idx_license_expires', 'expires_at'),
        Index('idx_license_active', 'is_active'),
    )


class Activation(Base):
    __tablename__ = "activations"

    id = Column(String(36), primary_key=True, index=True)
    license_id = Column(String(36), ForeignKey("licenses.id"), nullable=False)
    hwid = Column(String(255), nullable=False)
    ip_address = Column(String(45), nullable=False)  # IPv6 compatible length
    user_agent = Column(String(512), nullable=True)
    timestamp = Column(DateTime, server_default=func.now(), nullable=False)
    license = relationship("License", back_populates="activations")

    # Add indices for IP and timestamp
    __table_args__ = (
        Index('idx_activation_ip', 'ip_address'),
        Index('idx_activation_timestamp', 'timestamp'),
    )


class LicenseModification(Base):
    __tablename__ = "license_modifications"

    id = Column(String(36), primary_key=True, index=True)
    license_id = Column(String(36), ForeignKey("licenses.id"), nullable=False)
    action = Column(String(50), nullable=False)
    previous_state = Column(String(1024), nullable=False)
    new_state = Column(String(1024), nullable=False)
    timestamp = Column(DateTime, server_default=func.now(), nullable=False)
    admin_id = Column(String(255), nullable=False)
    license = relationship("License", back_populates="modifications")

    # Add indices for action and timestamp
    __table_args__ = (
        Index('idx_modification_action', 'action'),
        Index('idx_modification_timestamp', 'timestamp'),
    )


class ValidationAttempt(Base):
    __tablename__ = "validation_attempts"

    id = Column(String(36), primary_key=True, index=True)
    license_id = Column(String(36), index=True, nullable=False)
    ip_address = Column(String(45), nullable=False)  # IPv6 compatible length
    hwid = Column(String(255), nullable=False)
    timestamp = Column(DateTime, server_default=func.now(), nullable=False)
    is_successful = Column(Boolean, nullable=False)

    # Add indices for faster querying
    __table_args__ = (
        Index('idx_validation_license_success', 'license_id', 'is_successful'),
        Index('idx_validation_ip', 'ip_address'),
        Index('idx_validation_timestamp', 'timestamp'),
    )


class SecurityEvent(Base):
    __tablename__ = "security_events"

    id = Column(String(36), primary_key=True, index=True)
    event_type = Column(String(50), nullable=False)
    license_id = Column(String(36), nullable=True)
    ip_address = Column(String(45), nullable=True)  # IPv6 compatible length
    timestamp = Column(DateTime, server_default=func.now(), nullable=False)
    details = Column(Text, nullable=False)
    severity = Column(String(20), nullable=False, default="medium")  # low, medium, high, critical

    # Add indices for faster querying
    __table_args__ = (
        Index('idx_security_event_type', 'event_type'),
        Index('idx_security_timestamp', 'timestamp'),
        Index('idx_security_severity', 'severity'),
    )


class TweakConfiguration(Base):
    __tablename__ = "tweak_configurations"

    id = Column(String(36), primary_key=True, index=True)
    name = Column(String(255), unique=True, nullable=False)
    category = Column(String(100), nullable=False)
    registry_path = Column(String(512), nullable=True)
    registry_value = Column(String(512), nullable=True)
    command = Column(String(1024), nullable=True)
    description = Column(Text, nullable=False)
    is_premium = Column(Boolean, default=False, nullable=False)
    encrypted_data = Column(Text, nullable=True)
    version = Column(Integer, default=1, nullable=False)
    created_at = Column(DateTime, server_default=func.now(), nullable=False)
    updated_at = Column(DateTime, server_default=func.now(), onupdate=func.now(), nullable=False)

    # Add indices for faster querying
    __table_args__ = (
        Index('idx_tweak_category', 'category'),
        Index('idx_tweak_premium', 'is_premium'),
    )


class RefreshToken(Base):
    __tablename__ = "refresh_tokens"

    id = Column(String(36), primary_key=True, index=True)
    admin_id = Column(String(36), index=True)
    token = Column(String(255), unique=True, index=True)
    expires_at = Column(DateTime, nullable=False)
    created_at = Column(DateTime, server_default=func.now())
    is_revoked = Column(Boolean, default=False)

    __table_args__ = (
        Index('idx_token_admin', 'admin_id', 'is_revoked'),
    )


class BlacklistedIP(Base):
    __tablename__ = "blacklisted_ips"

    id = Column(String(36), primary_key=True, index=True)
    ip_address = Column(String(45), unique=True, index=True)
    reason = Column(String(255), nullable=False)
    created_at = Column(DateTime, server_default=func.now())
    expires_at = Column(DateTime, nullable=True)  # NULL means permanent

    __table_args__ = (
        Index('idx_blacklist_expires', 'expires_at'),
    )

    class WhitelistedIP(Base):
        __tablename__ = "whitelisted_ips"

        id = Column(String(36), primary_key=True, index=True)
        ip_address = Column(String(45), unique=True, index=True)
        description = Column(String(255), nullable=False)
        created_at = Column(DateTime, server_default=func.now())


# Create all tables in the database
Base.metadata.create_all(bind=engine)


# Dependency to get the database session
def get_db():
    db = SessionLocal()
    try:
        yield db
    finally:
        db.close()


# Middleware for rate limiting
class RateLimitMiddleware(BaseHTTPMiddleware):
    async def dispatch(self, request: Request, call_next):
        client_ip = request.client.host
        path = request.url.path

        # Check whitelist
        if redis_client.sismember("whitelist:ip", client_ip):
            return await call_next(request)

        # Check blacklist
        if redis_client.sismember("blacklist:ip", client_ip):
            return JSONResponse(
                status_code=403,
                content={"error": "IP address is blacklisted"}
            )

        # Get limit for endpoint
        limit = RATE_LIMIT_MAX_REQUESTS.get(path, RATE_LIMIT_MAX_REQUESTS["default"])

        # Create rate limit key
        rate_limit_key = f"ratelimit:{client_ip}:{path}"

        # Check if key exists
        current = redis_client.get(rate_limit_key)
        if current is None:
            # Create new key
            redis_client.set(rate_limit_key, 1, ex=RATE_LIMIT_WINDOW)
        else:
            # Increment key
            current = int(current)
            if current >= limit:
                # Log excessive requests
                logger.warning(
                    "Rate limit exceeded",
                    extra={
                        "ip_address": client_ip,
                        "path": path,
                        "limit": limit,
                        "current": current
                    }
                )
                return JSONResponse(
                    status_code=429,
                    content={"error": "Rate limit exceeded. Please try again later."}
                )
            redis_client.incr(rate_limit_key)

        # Continue processing request
        response = await call_next(request)
        return response


# Middleware for metrics collection
class MetricsMiddleware(BaseHTTPMiddleware):
    async def dispatch(self, request: Request, call_next):
        path = request.url.path
        method = request.method

        start_time = time.time()
        response = await call_next(request)
        duration = time.time() - start_time

        REQUEST_LATENCY.labels(method=method, endpoint=path).observe(duration)
        HTTP_REQUESTS.labels(method=method, endpoint=path, status=response.status_code).inc()

        return response

def rotate_api_keys():
    """Regenerates API keys periodically to prevent theft."""
    global ADMIN_API_KEY
    ADMIN_API_KEY = secrets.token_hex(32)
    redis_client.set("current_admin_key", ADMIN_API_KEY, ex=43200)  # 12 hours

# Start the rotation cycle
threading.Thread(target=lambda: [rotate_api_keys() or time.sleep(43200)], daemon=True).start()




# Add middleware
app.add_middleware(GZipMiddleware, minimum_size=1000)
app.add_middleware(CORSMiddleware,
                   allow_origins=["*"],
                   allow_credentials=True,
                   allow_methods=["*"],
                   allow_headers=["*"])
app.add_middleware(RateLimitMiddleware)
app.add_middleware(MetricsMiddleware)

# Security schemes
api_key_header = APIKeyHeader(name="X-API-Key")
oauth2_scheme = OAuth2PasswordBearer(tokenUrl="token")


# Authentication dependencies
async def validate_admin_api_key(api_key: str = Depends(api_key_header)):
    if api_key != ADMIN_API_KEY:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Invalid API key",
            headers={"WWW-Authenticate": "Bearer"},
        )
    return api_key


async def get_current_admin(
        token: str = Depends(oauth2_scheme),
        db: Session = Depends(get_db)
):
    credentials_exception = HTTPException(
        status_code=status.HTTP_401_UNAUTHORIZED,
        detail="Could not validate credentials",
        headers={"WWW-Authenticate": "Bearer"},
    )

    try:
        payload = kms.verify_jwt(token)
        username = payload.get("sub")
        if username is None:
            raise credentials_exception
    except Exception:
        raise credentials_exception

    admin = db.query(AdminUser).filter(AdminUser.username == username).first()
    if admin is None:
        raise credentials_exception
    if not admin.is_active:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Inactive user"
        )

    return admin


# Models for request validation
class UserCreate(BaseModel):
    email: EmailStr
    discord_id: Optional[str] = None


class LicenseCreate(BaseModel):
    user_id: str
    license_type: str


class LicenseActivate(BaseModel):
    license_id: str
    hwid: str


class LicenseValidate(BaseModel):
    license_id: str
    hwid: str


class TweakConfigCreate(BaseModel):
    name: str
    category: str
    registry_path: Optional[str] = None
    registry_value: Optional[str] = None
    command: Optional[str] = None
    description: str
    is_premium: bool = False
    encrypted_data: Optional[str] = None


class AdminLogin(BaseModel):
    username: str
    password: str
    mfa_code: Optional[str] = None


class TokenResponse(BaseModel):
    access_token: str
    token_type: str
    refresh_token: str


class RefreshTokenRequest(BaseModel):
    refresh_token: str


class SecurityCheckResponse(BaseModel):
    status: str
    issues: list = []
    suggestions: list = []


# Function to add an event to the security log
def log_security_event(
        db: Session,
        event_type: str,
        license_id: Optional[str] = None,
        ip_address: Optional[str] = None,
        details: str = "",
        severity: str = "medium"
):
    event = SecurityEvent(
        id=str(uuid.uuid4()),
        event_type=event_type,
        license_id=license_id,
        ip_address=ip_address,
        details=details,
        severity=severity
    )
    db.add(event)
    db.commit()

    # Add to Merkle tree for tamper-evident logging
    entry = {
        "id": event.id,
        "type": event_type,
        "license_id": license_id,
        "ip_address": ip_address,
        "timestamp": datetime.datetime.now(datetime.UTC).isoformat(),
        "details": details,
        "severity": severity
    }
    license_log_tree.add_leaf(entry)

    return event.id


# API Routes
@app.post("/api/admin/login")
async def admin_login(
        login_data: AdminLogin,
        db: Session = Depends(get_db)
):
    admin = db.query(AdminUser).filter(AdminUser.username == login_data.username).first()
    if not admin:
        # Use constant time comparison to prevent timing attacks
        pwd_context.verify("invalid", "$2b$12$" + "x" * 53)
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Invalid username or password"
        )

    if not admin.verify_password(login_data.password):
        # Log failed login attempt
        log_security_event(
            db=db,
            event_type="failed_admin_login",
            ip_address=None,  # In a real app, get from request
            details=f"Failed login attempt for admin {admin.username}",
            severity="medium"
        )
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Invalid username or password"
        )

    # Check MFA if enabled
    if admin.mfa_enabled:
        if not login_data.mfa_code:
            raise HTTPException(
                status_code=status.HTTP_401_UNAUTHORIZED,
                detail="MFA code required"
            )

        totp = pyotp.TOTP(admin.mfa_secret)
        if not totp.verify(login_data.mfa_code):
            log_security_event(
                db=db,
                event_type="invalid_mfa",
                ip_address=None,  # In a real app, get from request
                details=f"Invalid MFA code for admin {admin.username}",
                severity="high"
            )
            raise HTTPException(
                status_code=status.HTTP_401_UNAUTHORIZED,
                detail="Invalid MFA code"
            )

    # Update last login
    admin.last_login = datetime.datetime.now(datetime.UTC)
    db.commit()

    # Create tokens
    access_token_expires = datetime.timedelta(minutes=ACCESS_TOKEN_EXPIRE_MINUTES)
    raw_token = kms.create_jwt(data={"sub": admin.username}, expires_delta=access_token_expires)
    access_token = kms.fernet.encrypt(raw_token.encode()).decode()  # ENCRYPTING TOKEN

    refresh_token_expires = datetime.timedelta(days=REFRESH_TOKEN_EXPIRE_DAYS)
    refresh_token_value = secrets.token_hex(32)

    # Store refresh token
    refresh_token = RefreshToken(
        id=str(uuid.uuid4()),
        admin_id=admin.id,
        token=refresh_token_value,
        expires_at=datetime.datetime.now(datetime.UTC) + refresh_token_expires
    )
    db.add(refresh_token)
    db.commit()

    # Log successful login
    log_security_event(
        db=db,
        event_type="admin_login",
        ip_address=None,  # In a real app, get from request
        details=f"Admin {admin.username} logged in",
        severity="low"
    )

    return {
        "access_token": access_token,
        "token_type": "bearer",
        "refresh_token": refresh_token_value
    }


@app.post("/api/admin/refresh-token")
async def refresh_token(
        request: RefreshTokenRequest,
        db: Session = Depends(get_db)
):
    # Find the refresh token
    token = db.query(RefreshToken).filter(
        RefreshToken.token == request.refresh_token,
        RefreshToken.is_revoked == False,
        RefreshToken.expires_at > datetime.datetime.now(datetime.UTC)
    ).first()

    if not token:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Invalid or expired refresh token"
        )

    # Get admin user
    admin = db.query(AdminUser).filter(AdminUser.id == token.admin_id).first()
    if not admin or not admin.is_active:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="User inactive or not found"
        )

    # Create new access token
    access_token_expires = datetime.timedelta(minutes=ACCESS_TOKEN_EXPIRE_MINUTES)
    raw_token = kms.create_jwt(data={"sub": admin.username}, expires_delta=access_token_expires)
    access_token = kms.fernet.encrypt(raw_token.encode()).decode()  # ENCRYPTING TOKEN

    # Create new refresh token
    refresh_token_expires = datetime.timedelta(days=REFRESH_TOKEN_EXPIRE_DAYS)
    new_refresh_token_value = secrets.token_hex(32)

    # Store new refresh token
    new_refresh_token = RefreshToken(
        id=str(uuid.uuid4()),
        admin_id=admin.id,
        token=new_refresh_token_value,
        expires_at=datetime.datetime.now(datetime.UTC) + refresh_token_expires
    )

    # Revoke old token
    token.is_revoked = True

    db.add(new_refresh_token)
    db.commit()

    return {
        "access_token": access_token,
        "token_type": "bearer",
        "refresh_token": new_refresh_token_value
    }


@app.post("/api/admin/revoke-token")
async def revoke_token(
        request: RefreshTokenRequest,
        current_admin: AdminUser = Depends(get_current_admin),
        db: Session = Depends(get_db)
):
    # Find the refresh token
    token = db.query(RefreshToken).filter(
        RefreshToken.token == request.refresh_token,
        RefreshToken.admin_id == current_admin.id,
        RefreshToken.is_revoked == False
    ).first()

    if not token:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="Token not found"
        )

    # Revoke token
    token.is_revoked = True
    db.commit()

    # Log token revocation
    log_security_event(
        db=db,
        event_type="token_revoked",
        ip_address=None,  # In a real app, get from request
        details=f"Refresh token revoked for admin {current_admin.username}",
        severity="low"
    )

    return {"status": "success", "message": "Token revoked"}


@app.post("/api/users/create", dependencies=[Depends(validate_admin_api_key)])
async def create_user(
        user_data: UserCreate,
        db: Session = Depends(get_db)
):
    # Check if user already exists
    existing_user = db.query(User).filter(User.email == user_data.email).first()
    if existing_user:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="User already exists"
        )

    # Create new user
    user_id = str(uuid.uuid4())
    user = User(
        id=user_id,
        email=user_data.email,
        discord_id=user_data.discord_id
    )
    db.add(user)
    db.commit()
    db.refresh(user)

    # Log user creation
    log_security_event(
        db=db,
        event_type="user_created",
        details=f"User created with ID {user_id}",
        severity="low"
    )

    return {"id": user.id, "email": user.email, "message": "User created successfully"}


@app.post("/api/licenses/create", dependencies=[Depends(validate_admin_api_key)])
async def create_license(
        license_data: LicenseCreate,
        db: Session = Depends(get_db)
):
    # Check if user exists
    user = db.query(User).filter(User.id == license_data.user_id).first()
    if not user:
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="User not found"
        )

    # Check if user is banned
    if user.is_banned:
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="User is banned"
        )

    # Validate license type
    if license_data.license_type not in KEY_VALID_DAYS:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail=f"Invalid license type. Available types: {', '.join(KEY_VALID_DAYS.keys())}"
        )

    # Create license
    license_id = str(uuid.uuid4())
    expiry_days = KEY_VALID_DAYS[license_data.license_type]
    expires_at = datetime.datetime.now(datetime.UTC) + datetime.timedelta(days=expiry_days)

    new_license = License(
        id=license_id,
        user_id=user.id,
        license_type=license_data.license_type,
        expires_at=expires_at,
        is_active=True
    )
    db.add(new_license)
    db.commit()
    db.refresh(new_license)

    # Create license payload
    license_payload = {
        "id": new_license.id,
        "user_id": user.id,
        "email": user.email,
        "license_type": new_license.license_type,
        "created_at": new_license.created_at.isoformat(),
        "expires_at": new_license.expires_at.isoformat()
    }

    # Sign license
    signature = kms.sign_license(license_payload)

    # Log license creation
    log_security_event(
        db=db,
        event_type="license_created",
        license_id=new_license.id,
        details=f"License created for user {user.id}, type: {license_data.license_type}",
        severity="low"
    )

    return {
        "license_id": new_license.id,
        "user_id": user.id,
        "email": user.email,
        "license_type": new_license.license_type,
        "created_at": new_license.created_at.isoformat(),
        "expires_at": new_license.expires_at.isoformat(),
        "signature": signature
    }


@app.post("/api/licenses/activate")
async def activate_license(
        activation_data: LicenseActivate,
        request: Request,
        db: Session = Depends(get_db)
):
    # Get client IP
    ip = request.client.host
    user_agent = request.headers.get("user-agent", "Unknown")

    # Check if IP is blacklisted
    blacklisted = db.query(BlacklistedIP).filter(
        BlacklistedIP.ip_address == ip,
        (BlacklistedIP.expires_at > datetime.datetime.now(datetime.UTC)) | (BlacklistedIP.expires_at.is_(None))
    ).first()

    if blacklisted:
        # Log blacklisted attempt
        log_security_event(
            db=db,
            event_type="blacklisted_ip_attempt",
            license_id=activation_data.license_id,
            ip_address=ip,
            details=f"Activation attempt from blacklisted IP: {ip}",
            severity="high"
        )
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="Access denied"
        )

    # Get license
    license_obj = db.query(License).filter(License.id == activation_data.license_id).first()
    if not license_obj:
        # Log invalid license attempt
        log_security_event(
            db=db,
            event_type="invalid_license_activation",
            license_id=activation_data.license_id,
            ip_address=ip,
            details=f"Activation attempt with invalid license ID",
            severity="medium"
        )
        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="License not found"
        )

    # Check if license is active
    if not license_obj.is_active:
        # Log disabled license attempt
        log_security_event(
            db=db,
            event_type="inactive_license_activation",
            license_id=license_obj.id,
            ip_address=ip,
            details=f"Activation attempt with inactive license",
            severity="medium"
        )
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="License is not active"
        )

    # Check if license has expired
    if license_obj.expires_at < datetime.datetime.now(datetime.UTC):
        # Log expired license attempt
        log_security_event(
            db=db,
            event_type="expired_license_activation",
            license_id=license_obj.id,
            ip_address=ip,
            details=f"Activation attempt with expired license",
            severity="medium"
        )
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="License has expired"
        )

    # Check if user is banned
    user = db.query(User).filter(User.id == license_obj.user_id).first()
    if user.is_banned:
        # Log banned user attempt
        log_security_event(
            db=db,
            event_type="banned_user_activation",
            license_id=license_obj.id,
            ip_address=ip,
            details=f"Activation attempt from banned user: {user.id}",
            severity="high"
        )
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="User is banned"
        )

    # If license already has a HWID, check if it matches
    if license_obj.hwid and license_obj.hwid != activation_data.hwid:
        # Log HWID mismatch
        log_security_event(
            db=db,
            event_type="hwid_mismatch",
            license_id=license_obj.id,
            ip_address=ip,
            details=f"HWID mismatch during activation. Existing: {license_obj.hwid}, Provided: {activation_data.hwid}",
            severity="high"
        )
        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="License is already activated on another device"
        )

    # Record activation
    activation = Activation(
        id=str(uuid.uuid4()),
        license_id=license_obj.id,
        hwid=activation_data.hwid,
        ip_address=ip,
        user_agent=user_agent
    )
    db.add(activation)

    # Set HWID if not already set
    if not license_obj.hwid:
        license_obj.hwid = activation_data.hwid

    db.commit()

    # Create license payload
    license_payload = {
        "id": license_obj.id,
        "user_id": user.id,
        "email": user.email,
        "license_type": license_obj.license_type,
        "created_at": license_obj.created_at.isoformat(),
        "expires_at": license_obj.expires_at.isoformat(),
        "hwid": license_obj.hwid
    }

    # Sign license
    signature = kms.sign_license(license_payload)

    # Log successful activation
    log_security_event(
        db=db,
        event_type="license_activated",
        license_id=license_obj.id,
        ip_address=ip,
        details=f"License successfully activated with HWID: {activation_data.hwid}",
        severity="low"
    )

    return {
        "license_id": license_obj.id,
        "user_id": user.id,
        "email": user.email,
        "license_type": license_obj.license_type,
        "created_at": license_obj.created_at.isoformat(),
        "expires_at": license_obj.expires_at.isoformat(),
        "hwid": license_obj.hwid,
        "signature": signature
    }


@app.post("/api/license/validate")
async def validate_license(
        validation_data: LicenseValidate,
        request: Request,
        background_tasks: BackgroundTasks,  # Move this up
        db: Session = Depends(get_db)
):
    # Get client IP
    ip = request.client.host

    # Check if IP is blacklisted
    blacklisted = db.query(BlacklistedIP).filter(
        BlacklistedIP.ip_address == ip,
        (BlacklistedIP.expires_at > datetime.datetime.now(datetime.UTC)) | (BlacklistedIP.expires_at.is_(None))
    ).first()

    if blacklisted:
        # Log blacklisted attempt
        log_security_event(
            db=db,
            event_type="blacklisted_ip_validation",
            license_id=validation_data.license_id,
            ip_address=ip,
            details=f"Validation attempt from blacklisted IP: {ip}",
            severity="high"
        )

        # Record failed validation
        validation_attempt = ValidationAttempt(
            id=str(uuid.uuid4()),
            license_id=validation_data.license_id,
            ip_address=ip,
            hwid=validation_data.hwid,
            is_successful=False
        )
        db.add(validation_attempt)
        db.commit()

        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="Access denied"
        )

    # Get license
    license_obj = db.query(License).filter(License.id == validation_data.license_id).first()
    if not license_obj:
        # Log invalid license attempt
        log_security_event(
            db=db,
            event_type="invalid_license_validation",
            license_id=validation_data.license_id,
            ip_address=ip,
            details=f"Validation attempt with invalid license ID",
            severity="medium"
        )

        # Record failed validation
        validation_attempt = ValidationAttempt(
            id=str(uuid.uuid4()),
            license_id=validation_data.license_id,
            ip_address=ip,
            hwid=validation_data.hwid,
            is_successful=False
        )
        db.add(validation_attempt)
        db.commit()

        raise HTTPException(
            status_code=status.HTTP_404_NOT_FOUND,
            detail="License not found"
        )

    # Check if license is active
    if not license_obj.is_active:
        # Log disabled license attempt
        log_security_event(
            db=db,
            event_type="inactive_license_validation",
            license_id=license_obj.id,
            ip_address=ip,
            details=f"Validation attempt with inactive license",
            severity="medium"
        )

        # Record failed validation
        validation_attempt = ValidationAttempt(
            id=str(uuid.uuid4()),
            license_id=license_obj.id,
            ip_address=ip,
            hwid=validation_data.hwid,
            is_successful=False
        )
        db.add(validation_attempt)
        db.commit()

        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="License is not active"
        )

    # Check if license has expired
    if license_obj.expires_at < datetime.datetime.now(datetime.UTC):
        # Log expired license attempt
        log_security_event(
            db=db,
            event_type="expired_license_validation",
            license_id=license_obj.id,
            ip_address=ip,
            details=f"Validation attempt with expired license",
            severity="medium"
        )

        # Record failed validation
        validation_attempt = ValidationAttempt(
            id=str(uuid.uuid4()),
            license_id=license_obj.id,
            ip_address=ip,
            hwid=validation_data.hwid,
            is_successful=False
        )
        db.add(validation_attempt)
        db.commit()

        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="License has expired"
        )

    # Check if user is banned
    user = db.query(User).filter(User.id == license_obj.user_id).first()
    if user.is_banned:
        # Log banned user attempt
        log_security_event(
            db=db,
            event_type="banned_user_validation",
            license_id=license_obj.id,
            ip_address=ip,
            details=f"Validation attempt from banned user: {user.id}",
            severity="high"
        )

        # Record failed validation
        validation_attempt = ValidationAttempt(
            id=str(uuid.uuid4()),
            license_id=license_obj.id,
            ip_address=ip,
            hwid=validation_data.hwid,
            is_successful=False
        )
        db.add(validation_attempt)
        db.commit()

        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="User is banned"
        )

    # If license has a HWID, check if it matches
    if license_obj.hwid and license_obj.hwid != validation_data.hwid:
        # Log HWID mismatch
        log_security_event(
            db=db,
            event_type="hwid_mismatch_validation",
            license_id=license_obj.id,
            ip_address=ip,
            details=f"HWID mismatch during validation. Existing: {license_obj.hwid}, Provided: {validation_data.hwid}",
            severity="high"
        )

        # Record failed validation
        validation_attempt = ValidationAttempt(
            id=str(uuid.uuid4()),
            license_id=license_obj.id,
            ip_address=ip,
            hwid=validation_data.hwid,
            is_successful=False
        )
        db.add(validation_attempt)
        db.commit()

        # Background task to check for repeated failures
        background_tasks.add_task(check_for_anomalies, license_obj.id, ip)

        raise HTTPException(
            status_code=status.HTTP_403_FORBIDDEN,
            detail="License is activated on another device"
        )

    # Record successful validation
    validation_attempt = ValidationAttempt(
        id=str(uuid.uuid4()),
        license_id=license_obj.id,
        ip_address=ip,
        hwid=validation_data.hwid,
        is_successful=True
    )
    db.add(validation_attempt)
    db.commit()

    # Create license payload
    license_payload = {
        "id": license_obj.id,
        "user_id": user.id,
        "email": user.email,
        "license_type": license_obj.license_type,
        "created_at": license_obj.created_at.isoformat(),
        "expires_at": license_obj.expires_at.isoformat(),
        "hwid": license_obj.hwid,
        "validated_at": datetime.datetime.now(datetime.UTC).isoformat()
    }

    # Sign license
    signature = kms.sign_license(license_payload)

    return {
        "license_id": license_obj.id,
        "user_id": user.id,
        "email": user.email,
        "license_type": license_obj.license_type,
        "created_at": license_obj.created_at.isoformat(),
        "expires_at": license_obj.expires_at.isoformat(),
        "hwid": license_obj.hwid,
        "validated_at": license_payload["validated_at"],
        "signature": signature,
        "is_valid": True
    }


# Background task to check for anomalies
def check_for_anomalies(license_id: str, ip_address: str):
    db = SessionLocal()
    try:
        # Check for repeated validation failures
        recent_failures = db.query(ValidationAttempt).filter(
            ValidationAttempt.license_id == license_id,
            ValidationAttempt.is_successful == False,
            ValidationAttempt.created_at > datetime.datetime.now(datetime.UTC) - datetime.timedelta(hours=24)
        ).count()

        # If more than 5 failures in 24 hours
        if recent_failures >= 5:
            # Log security event
            log_security_event(
                db=db,
                event_type="repeated_validation_failures",
                license_id=license_id,
                ip_address=ip_address,
                details=f"Multiple validation failures detected: {recent_failures} in last 24 hours",
                severity="high"
            )

            # Blacklist IP temporarily
            blacklist_ip = BlacklistedIP(
                id=str(uuid.uuid4()),
                ip_address=ip_address,
                reason="Repeated validation failures",
                expires_at=datetime.datetime.now(datetime.UTC) + datetime.timedelta(hours=12)
            )
            db.add(blacklist_ip)
            db.commit()

            # Send alert to admin (in a real app)
            # admin_notification_service.send_alert(f"Potential license theft attempt: {license_id}")

        # Check for multiple IPs using same license
        distinct_ips = db.query(ValidationAttempt.ip_address).distinct().filter(
            ValidationAttempt.license_id == license_id,
            ValidationAttempt.created_at > datetime.datetime.now(datetime.UTC) - datetime.timedelta(hours=24)
        ).count()

        if distinct_ips > 3:  # If used from more than 3 different IPs in 24 hours
            # Log security event
            log_security_event(
                db=db,
                event_type="multiple_ip_usage",
                license_id=license_id,
                ip_address=ip_address,
                details=f"License used from {distinct_ips} different IPs in last 24 hours",
                severity="high"
            )

            # Get the license
            license_obj = db.query(License).filter(License.id == license_id).first()
            if license_obj:
                # Flag license for review
                license_obj.needs_review = True
                db.commit()

                # Send alert to admin (in a real app)
                # admin_notification_service.send_alert(f"Suspicious license usage: {license_id}")

    finally:
        db.close()


@app.post("/api/admin/security-check")
async def security_check(
        current_admin: AdminUser = Depends(get_current_admin),
        db: Session = Depends(get_db)
):
    """Run a security check on the system and return findings"""
    issues = []
    suggestions = []

    # Check for outdated refresh tokens
    old_tokens = db.query(RefreshToken).filter(
        RefreshToken.is_revoked == False,
        RefreshToken.created_at < datetime.datetime.now(datetime.UTC) - datetime.timedelta(days=30)
    ).count()

    if old_tokens > 0:
        issues.append(f"Found {old_tokens} refresh tokens older than 30 days")
        suggestions.append("Revoke old refresh tokens regularly")

    # Check for licenses that need review
    licenses_needing_review = db.query(License).filter(
        License.needs_review == True
    ).count()

    if licenses_needing_review > 0:
        issues.append(f"{licenses_needing_review} licenses flagged for review")
        suggestions.append("Review flagged licenses for suspicious activity")

    # Check for recent failed login attempts
    recent_failed_logins = db.query(SecurityEvent).filter(
        SecurityEvent.event_type == "failed_admin_login",
        SecurityEvent.created_at > datetime.datetime.now(datetime.UTC) - datetime.timedelta(days=1)
    ).count()

    if recent_failed_logins > 10:
        issues.append(f"{recent_failed_logins} failed admin login attempts in last 24 hours")
        suggestions.append("Consider implementing additional login protections")

    # Check for admins without MFA
    admins_without_mfa = db.query(AdminUser).filter(
        AdminUser.mfa_enabled == False
    ).count()

    if admins_without_mfa > 0:
        issues.append(f"{admins_without_mfa} admin accounts without MFA enabled")
        suggestions.append("Require MFA for all admin accounts")

    # Log security check
    log_security_event(
        db=db,
        event_type="security_audit",
        details=f"Security check performed by admin {current_admin.username}",
        severity="low"
    )

    return SecurityCheckResponse(
        status="complete",
        issues=issues,
        suggestions=suggestions
    )


@app.post("/api/tweak-configs/create", dependencies=[Depends(get_current_admin)])
async def create_tweak_config(
        config_data: TweakConfigCreate,
        db: Session = Depends(get_db)
):
    """Create a new tweak configuration"""
    # Check if config with same name exists
    existing_config = db.query(TweakConfiguration).filter(TweakConfiguration.name == config_data.name).first()
    if existing_config:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="Config with this name already exists"
        )

    # Validate config data
    if config_data.registry_path and not config_data.registry_value:
        raise HTTPException(
            status_code=status.HTTP_400_BAD_REQUEST,
            detail="Registry value required when registry path is provided"
        )

    # Create new config
    config_id = str(uuid.uuid4())
    config = TweakConfiguration(
        id=config_id,
        name=config_data.name,
        category=config_data.category,
        registry_path=config_data.registry_path,
        registry_value=config_data.registry_value,
        command=config_data.command,
        description=config_data.description,
        is_premium=config_data.is_premium
    )

    # If encrypted data is provided, encrypt and store it
    if config_data.encrypted_data:
        config.encrypted_data = kms.encrypt_data(config_data.encrypted_data)

    db.add(config)
    db.commit()
    db.refresh(config)

    # Log config creation
    log_security_event(
        db=db,
        event_type="config_created",
        details=f"Tweak config created: {config.name}",
        severity="low"
    )

    return {
        "id": config.id,
        "name": config.name,
        "category": config.category,
        "description": config.description,
        "is_premium": config.is_premium,
        "created_at": config.created_at.isoformat()
    }


@app.get("/api/tweak-configs")
async def get_tweak_configs(
        license_id: str,
        hwid: str,
        request: Request,
        db: Session = Depends(get_db)
):
    """Get available tweak configurations for a license"""
    # Get client IP
    ip = request.client.host

    # Validate license
    validation_data = LicenseValidate(license_id=license_id, hwid=hwid)
    try:
        validation_result = await validate_license(
            validation_data=validation_data,
            request=request,
            db=db,
            background_tasks=BackgroundTasks()
        )
    except HTTPException:
        # Return only free tweaks if license validation fails
        configs = db.query(TweakConfiguration).filter(
            TweakConfiguration.is_active == True,
            TweakConfiguration.is_premium == False
        ).all()

        return {
            "valid_license": False,
            "message": "Using free tweaks only",
            "configs": [
                {
                    "id": config.id,
                    "name": config.name,
                    "category": config.category,
                    "description": config.description,
                    "is_premium": config.is_premium
                } for config in configs
            ]
        }

    # License is valid, get license object
    license_obj = db.query(License).filter(License.id == license_id).first()

    # Get all active configs
    configs = db.query(TweakConfiguration).filter(
        TweakConfiguration.is_active == True
    ).all()

    # Filter premium configs based on license type
    result_configs = []
    for config in configs:
        # Include all non-premium configs
        if not config.is_premium:
            result_configs.append(config)
        # Include premium configs only for premium licenses
        elif license_obj.license_type in ["premium", "enterprise"]:
            result_configs.append(config)

    # Log tweak configs access
    log_security_event(
        db=db,
        event_type="configs_accessed",
        license_id=license_id,
        ip_address=ip,
        details=f"Tweak configs accessed, returned {len(result_configs)} configs",
        severity="low"
    )

    return {
        "valid_license": True,
        "license_type": license_obj.license_type,
        "configs": [
            {
                "id": config.id,
                "name": config.name,
                "category": config.category,
                "description": config.description,
                "is_premium": config.is_premium,
                "registry_path": config.registry_path,
                "registry_value": config.registry_value,
                "command": config.command,
                "encrypted_data": kms.decrypt_data(config.encrypted_data) if config.encrypted_data else None
            } for config in result_configs
        ]
    }


@app.get("/api/admin/audit-log", dependencies=[Depends(get_current_admin)])
async def get_audit_log(
        event_type: Optional[str] = None,
        severity: Optional[str] = None,
        start_date: Optional[str] = None,
        end_date: Optional[str] = None,
        limit: int = 100,
        db: Session = Depends(get_db)
):
    """Get security audit log with optional filters"""
    query = db.query(SecurityEvent)

    # Apply filters
    if event_type:
        query = query.filter(SecurityEvent.event_type == event_type)

    if severity:
        query = query.filter(SecurityEvent.severity == severity)

    if start_date:
        try:
            start_datetime = datetime.datetime.fromisoformat(start_date)
            query = query.filter(SecurityEvent.created_at >= start_datetime)
        except ValueError:
            raise HTTPException(
                status_code=status.HTTP_400_BAD_REQUEST,
                detail="Invalid start_date format. Use ISO format (YYYY-MM-DDTHH:MM:SS)"
            )

    if end_date:
        try:
            end_datetime = datetime.datetime.fromisoformat(end_date)
            query = query.filter(SecurityEvent.created_at <= end_datetime)
        except ValueError:
            raise HTTPException(
                status_code=status.HTTP_400_BAD_REQUEST,
                detail="Invalid end_date format. Use ISO format (YYYY-MM-DDTHH:MM:SS)"
            )

    # Order by created_at (newest first) and limit results
    events = query.order_by(SecurityEvent.created_at.desc()).limit(limit).all()

    # Verify log integrity using Merkle tree
    for event in events:
        event_data = {
            "id": event.id,
            "type": event.event_type,
            "license_id": event.license_id,
            "ip_address": event.ip_address,
            "timestamp": event.created_at.isoformat(),
            "details": event.details,
            "severity": event.severity
        }

        # Check if event is in the Merkle tree
        event.verified = license_log_tree.verify_leaf(event_data)

    return {
        "count": len(events),
        "events": [
            {
                "id": event.id,
                "event_type": event.event_type,
                "license_id": event.license_id,
                "ip_address": event.ip_address,
                "details": event.details,
                "severity": event.severity,
                "created_at": event.created_at.isoformat(),
                "verified": getattr(event, "verified", False)
            } for event in events
        ]
    }


@app.get("/metrics", dependencies=[Depends(validate_admin_api_key)])
async def get_metrics():
    """Return Prometheus metrics"""
    return Response(
        content=generate_latest().decode("utf-8"),
        media_type="text/plain"
    )


# Startup and shutdown events
@app.on_event("startup")
async def startup_event():
    # Initialize database
    Base.metadata.create_all(bind=engine)

    # Initialize Prometheus metrics
    HTTP_REQUESTS.labels(method="GET", endpoint="/metrics", status=200).inc(0)
    REQUEST_LATENCY.labels(method="GET", endpoint="/metrics").observe(0.0)

    # Log application startup
    db = SessionLocal()
    try:
        log_security_event(
            db=db,
            event_type="application_startup",
            details="License Management API started",
            severity="low"
        )
    finally:
        db.close()


@app.on_event("shutdown")
async def shutdown_event():
    # Log application shutdown
    db = SessionLocal()
    try:
        log_security_event(
            db=db,
            event_type="application_shutdown",
            details="License Management API shutdown",
            severity="low"
        )
    finally:
        db.close()


# Exception handlers
@app.exception_handler(Exception)
async def global_exception_handler(request: Request, exc: Exception):
    # Log unhandled exceptions
    db = SessionLocal()
    try:
        log_security_event(
            db=db,
            event_type="unhandled_exception",
            details=f"Unhandled exception: {str(exc)}",
            severity="high"
        )
    finally:
        db.close()

    # Return error response
    return JSONResponse(
        status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
        content={"detail": "An internal error occurred"}
    )


# Main entry point
if __name__ == "__main__":
    import uvicorn

    # Load environment variables
    load_dotenv()

    # Get port from environment or use default
    port = int(os.getenv("PORT", "8000"))

    # Run application
    uvicorn.run(
        "main:app",
        host="0.0.0.0",
        port=port,
        reload=False,
        workers=4,
        log_level="info"
    )